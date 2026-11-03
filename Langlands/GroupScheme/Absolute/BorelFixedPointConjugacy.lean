import Langlands.GroupScheme.Absolute.BorelTransport
import Langlands.GroupScheme.FixedCosetFactorization
import Langlands.GroupScheme.SchemeAction
import Langlands.AbelianScheme.AlgClosedIsogenyPointLifting

/-! # Actual Borel conjugacy data from a fixed quotient point -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {B B' G : GroupScheme (Spec (CommRingCat.of k))}
variable {i : B ⟶ G} {i' : B' ⟶ G}
variable (hi : IsBorelSubgroup i) (hi' : IsBorelSubgroup i')
variable {Q : Over (Spec (CommRingCat.of k))} (q : G.X ⟶ Q)
variable [LocallyOfFiniteType q.left] [Surjective q.left]
variable (hfib : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
  g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i').carrier T)
variable (a : SchemeAction G Q)
variable (hact : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
  a.act g (h ≫ q) = (g * h) ≫ q)

/-- A fixed rational quotient point supplies actual conjugating data. -/
def IsBorelSubgroup.conjugatingDataOfFixedPoint
    (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Q)
    (hfixed : (a.restrict i).IsFixed x) :
    Σ (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X),
      {φ : B ≅ B' // i ≫ (G.innerIso g).hom = φ.hom ≫ i'} := by
  classical
  let hlift := Langlands.exists_point_lift_of_locallyOfFiniteType_surjective q.left x.left
  let g₀ := Classical.choose hlift
  have hg₀ : g₀ ≫ q.left = x.left := Classical.choose_spec hlift
  have hgS : g₀ ≫ G.X.hom = 𝟙 (Spec (CommRingCat.of k)) := by
    rw [← Over.w q, ← Category.assoc, hg₀]
    exact Over.w x
  let g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X := Over.homMk g₀ hgS
  have hg : g ≫ q = x := Over.OverMorphism.ext hg₀
  have hcoset : ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ B.X),
      ((h ≫ i.hom.hom) * G.constantPoint g T) ≫ q = G.constantPoint g T ≫ q := by
    intro T h
    have e := hfixed T (Over.homMk T.hom (by simp)) h
    rw [SchemeAction.restrict_act, ← hg, ← Category.assoc] at e
    change a.act (h ≫ i.hom.hom) (G.constantPoint g T ≫ q) =
      G.constantPoint g T ≫ q at e
    rwa [hact] at e
  have : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  have : IsClosedImmersion i'.hom.hom.left := hi'.isClosedSubgroup
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have : Mono i'.hom.hom := Over.mono_of_mono_left _
  let f := factorOfFixedCoset i i' q hfib g hcoset
  have hf : f ≫ i' = i ≫ (G.innerIso g⁻¹).hom :=
    factorOfFixedCoset_comp i i' q hfib g hcoset
  exact ⟨g⁻¹, hi.conjugatingIsoOfFactor hi' g⁻¹ f hf, hf.symm⟩

end Langlands.GroupScheme
