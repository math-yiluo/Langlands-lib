import Langlands.GroupScheme.Absolute.BorelConjugacyProof
import Langlands.GroupScheme.ParabolicQuotientProperReduction

/-! # Properness of surjective maps constant on Borel cosets -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] [IsAlgClosed k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]

/-- A separated, locally finite type target of a surjective map from `G`
constant on the right cosets of an actual Borel is proper. -/
theorem isProper_of_borel_coset
    {B : GroupScheme (Spec (CommRingCat.of k))}
    (b : B ⟶ G) (hb : IsBorelSubgroup b)
    {Q : Over (Spec (CommRingCat.of k))} (q : G.X ⟶ Q)
    [IsSeparated Q.hom] [LocallyOfFiniteType Q.hom] [Surjective q.left]
    (hq : ∀ (T : Over (Spec (CommRingCat.of k))) (x y : T ⟶ G.X),
      x⁻¹ * y ∈ (SubgroupFunctor.range b).carrier T → x ≫ q = y ≫ q) :
    IsProper Q.hom := by
  obtain ⟨B₀, b₀, hb₀, hproper⟩ := someBorelQuotientProper k G inferInstance
  obtain ⟨Q₀, q₀, hsep₀, hft₀, hqc₀, hsm₀, hsurj₀, hqqc₀, hfib₀⟩ :=
    smoothSubgroupQuotientExistence k G B₀ b₀ hb₀.isClosedSubgroup hb₀.smooth
  let : Smooth q₀.left := hsm₀
  let : Surjective q₀.left := hsurj₀
  let : QuasiCompact q₀.left := hqqc₀
  let : IsProper Q₀.hom :=
    hproper Q₀ q₀ hsep₀ hft₀ hqc₀ hsm₀ hsurj₀ hqqc₀ hfib₀
  obtain ⟨g, φ, hg⟩ := (borelConjugacy k G).2 B₀ B b₀ b hb₀ hb
  let a := (G.innerIso g).hom.hom.hom
  obtain ⟨d, hd⟩ := ParabolicQuotient.exists_factor b₀ q₀ (a ≫ q)
    (fun T x y h => (hfib₀ T x y).mp h)
    (ParabolicQuotient.innerIso_coset b₀ b g φ.hom hg q hq)
  have : IsIso a.left := isIso_left_of_iso (G.innerIso g)
  have : Surjective (q₀.left ≫ d.left) := by
    rw [← Over.comp_left, hd, Over.comp_left]
    infer_instance
  have : Surjective d.left := Surjective.of_comp q₀.left d.left
  have : UniversallyClosed Q.hom :=
    ParabolicQuotient.universallyClosed_of_surjective d
  exact ⟨⟩

end Langlands.GroupScheme
