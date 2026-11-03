import Langlands.GroupScheme.Absolute.BorelExistence
import Langlands.GroupScheme.Absolute.BorelTransport
import Langlands.GroupScheme.FixedCosetFactorization
import Langlands.GroupScheme.Dynamic.FlagQuotientSchemeAction
import Langlands.GroupScheme.SolvableProperFixedPointStatement
import Langlands.AbelianScheme.AlgClosedIsogenyPointLifting

/-! # Borel maximality from a proper solvable homogeneous quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- A smooth connected solvable closed subgroup with a proper actual homogeneous
quotient is Borel. This is the implication (b) ⇒ (a) of Milne 2017, 17.19. -/
def ProperSolvableQuotientBorelStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom],
    ConnectedSpace G.X.left →
    ∀ (H : GroupScheme (Spec (CommRingCat.of k))) (i : H ⟶ G),
      IsClosedSubgroup i → Smooth H.X.hom → ConnectedSpace H.X.left →
      IsSolvableGroupScheme H →
      ∀ (Q : Over (Spec (CommRingCat.of k))) (q : G.X ⟶ Q),
        IsProper Q.hom → Smooth q.left → Surjective q.left → QuasiCompact q.left →
        (∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
          g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T) →
        IsBorelSubgroup i

section FixedPoint

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {B H G : GroupScheme (Spec (CommRingCat.of k))}
variable {b : B ⟶ G} (hb : IsBorelSubgroup b)
variable {i : H ⟶ G} (hi : IsClosedSubgroup i)
variable (hsm : Smooth H.X.hom) (hconn : ConnectedSpace H.X.left)
variable (hsol : IsSolvableGroupScheme H)
variable {Q : Over (Spec (CommRingCat.of k))} (q : G.X ⟶ Q)
variable [LocallyOfFiniteType q.left] [Surjective q.left]
variable (hfib : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
  g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T)
variable (a : SchemeAction G Q)
variable (hact : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
  a.act g (h ≫ q) = (g * h) ≫ q)

include hb hi hsm hconn hsol hfib hact

/-- A fixed rational quotient point for one Borel makes the stabilizer Borel,
provided the stabilizer is smooth, connected and solvable. -/
theorem IsBorelSubgroup.of_fixedQuotientPoint
    (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Q)
    (hfixed : (a.restrict b).IsFixed x) : IsBorelSubgroup i := by
  classical
  obtain ⟨g₀, hg₀⟩ :=
    Langlands.exists_point_lift_of_locallyOfFiniteType_surjective q.left x.left
  have hgS : g₀ ≫ G.X.hom = 𝟙 (Spec (CommRingCat.of k)) := by
    rw [← Over.w q, ← Category.assoc, hg₀]
    exact Over.w x
  let g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X := Over.homMk g₀ hgS
  have hg : g ≫ q = x := Over.OverMorphism.ext hg₀
  have hcoset : ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ B.X),
      ((h ≫ b.hom.hom) * G.constantPoint g T) ≫ q = G.constantPoint g T ≫ q := by
    intro T h
    have e := hfixed T (Over.homMk T.hom (by simp)) h
    rw [SchemeAction.restrict_act, ← hg, ← Category.assoc] at e
    change a.act (h ≫ b.hom.hom) (G.constantPoint g T ≫ q) =
      G.constantPoint g T ≫ q at e
    rwa [hact] at e
  have : IsClosedImmersion b.hom.hom.left := hb.isClosedSubgroup
  have : IsClosedImmersion i.hom.hom.left := hi
  have : Mono b.hom.hom := Over.mono_of_mono_left _
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  let f := factorOfFixedCoset b i q hfib g hcoset
  have hf : f ≫ i = b ≫ (G.innerIso g⁻¹).hom :=
    factorOfFixedCoset_comp b i q hfib g hcoset
  have hb' := hb.comp_iso (G.innerIso g⁻¹)
  have : IsIso f := hb'.maximal H i f hi hsm hconn hsol hf
  have he : (asIso f).inv ≫ (b ≫ (G.innerIso g⁻¹).hom) = i := by
    rw [← hf]
    change (asIso f).inv ≫ (asIso f).hom ≫ i = i
    exact (asIso f).inv_hom_id_assoc i
  have htransport := hb'.iso_comp (asIso f).symm
  change IsBorelSubgroup ((asIso f).inv ≫ (b ≫ (G.innerIso g⁻¹).hom)) at htransport
  rwa [he] at htransport

end FixedPoint

/-- The general solvable fixed-point theorem implies the proper solvable
homogeneous quotient criterion, using the actual descended quotient action. -/
theorem properSolvableQuotientBorel_of_solvableProperFixedPoint
    (hfixed : SolvableProperFixedPointStatement.{u}) :
    ProperSolvableQuotientBorelStatement.{u} := by
  intro k _ _ G _ _ hGconn H i hi hsm hconn hsol Q q hproper hqsm hqsurj hqqc hfib
  have := hGconn
  have := hqsm
  have := hqsurj
  have := hqqc
  obtain ⟨B, b, hb⟩ := BorelExistence.exists_isBorelSubgroup G
  have : IsClosedImmersion b.hom.hom.left := hb.isClosedSubgroup
  have : Smooth B.X.hom := hb.smooth
  have : IsAffineHom B.X.hom := by
    rw [← Over.w b.hom.hom]
    infer_instance
  let a := Dynamic.flagQuotientSchemeAction G (SubgroupFunctor.range i) q hfib
  have hn : Nonempty Q.left := Nonempty.map q.left inferInstance
  obtain ⟨x, hx⟩ :=
    hfixed k B hb.connectedSpace hb.isSolvableGroupScheme Q hproper hn (a.restrict b)
  exact hb.of_fixedQuotientPoint hi hsm hconn hsol q hfib a
    (fun _ g h => Dynamic.flagQuotientSchemeAction_act_lift G
      (SubgroupFunctor.range i) q hfib g h) x hx

end Langlands.GroupScheme
