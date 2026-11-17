import Langlands.GroupScheme.Reductive.AffinePinnedAutomorphismPredicate
import Langlands.GroupScheme.Reductive.AffinePinnedCoefficientRigidity
import Langlands.GroupScheme.Reductive.AlignedWeightLineUnits
import Langlands.GroupScheme.Reductive.StarActionIndependenceProof

/-! # Exact affine pinning from global coordinate alignment and local pinning -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace splitTorus

/-- One field-valued point makes the fixed integral exponent characters
injective, without requiring the base to be reduced or connected. -/
theorem exponentCharacter_injective_of_field_point
    {S : Scheme.{u}} (I : Type u) [Fintype I]
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S) :
    Function.Injective (exponentCharacter S I) := by
  intro m n h
  have hc : exponentCharacter (Spec (CommRingCat.of k)) I m =
      exponentCharacter (Spec (CommRingCat.of k)) I n := by
    apply (cancel_epi (commBaseChangeIso b I).hom).mp
    rw [exponentCharacter_baseChange, exponentCharacter_baseChange, h]
  have he := congrArg (characterLatticeEquiv k I) hc
  simpa only [exponentCharacter_eq_characterLatticeEquiv_symm,
    AddEquiv.apply_symm_apply] using he

end splitTorus

namespace BasedCoordinateIso

variable {S : Scheme.{u}} {I I' J J' : Type u}
  [Fintype I] [Fintype I'] [Fintype J] [Fintype J']
  {G H : GroupScheme S}
  {i : splitTorus S I ⟶ G} {j : splitTorus S I' ⟶ H}
  {P : RootDatum J (I → ℤ) (I → ℤ)} {Q : RootDatum J' (I' → ℤ) (I' → ℤ)}
  {b : P.Base} {c : Q.Base}

omit [Fintype J] [Fintype J'] in
/-- The all-test character clause is the exact equality of actual integral
characters in the commutative group-scheme category. -/
theorem exponentCharacter_comp (d : BasedCoordinateIso i j P Q b c) (m : I' → ℤ) :
    (CommGroupScheme.isoOfGroupIso d.torusIso).hom ≫
        splitTorus.exponentCharacter S I' m =
      splitTorus.exponentCharacter S I (d.rootEquiv.weightMap m) := by
  apply Additive.toMul.injective
  change d.torusIso.hom ≫
      CommGroupScheme.groupHom (splitTorus.exponentCharacter S I' m) =
    CommGroupScheme.groupHom (splitTorus.exponentCharacter S I (d.rootEquiv.weightMap m))
  apply hom_ext_points
  intro U x
  apply (Gm.pointsEquiv S U).injective
  simpa only [Grp.comp_hom_hom, ← Category.assoc,
    splitTorus.pointsEquiv_exponentCharacter] using d.characters U x m

end BasedCoordinateIso

namespace AffinePinnedModel

variable (M : AffinePinnedModel.{u})

/-- Global full based coordinate data and concrete local pinning force the
exact affine pinned automorphism predicate, with the inverse coordinate label. -/
theorem isPinnedAutomorphism_of_basedCoordinateIso
    (d : BasedCoordinateIso M.inclusion M.inclusion
      M.rootDatum M.rootDatum M.basis M.basis)
    (hpin : PreservesLocalPinning ((baseChange (𝟙 M.base)).mapIso d.groupIso)) :
    M.IsPinnedAutomorphism d.groupIso d.rootEquiv⁻¹ := by
  classical
  have hr : d.rootEquiv ∈ M.basedAutomorphisms := d.simple_iff
  have hθ : d.rootEquiv⁻¹ ∈ M.basedAutomorphisms :=
    M.basedAutomorphisms.inv_mem hr
  refine ⟨hθ, ⟨d.torusIso, d.square, ?_⟩, ?_⟩
  · intro U x m
    change (∏ j, splitTorus.pointsEquiv M.coordinates U
      (x ≫ d.torusIso.hom.hom.hom) j ^ d.rootEquiv.weightEquiv.symm m j) =
        ∏ j, splitTorus.pointsEquiv M.coordinates U x j ^ m j
    simpa only [RootPairing.Equiv.weightMap_weightEquiv_symm] using
      d.characters U x (d.rootEquiv.weightEquiv.symm m)
  · intro s
    let t : M.basis.support :=
      ⟨(d.rootEquiv⁻¹).indexEquiv s, (hθ s).mp s.property⟩
    let τ : splitTorus.commGroupScheme M.base M.coordinates ≅
        splitTorus.commGroupScheme M.base M.coordinates :=
      CommGroupScheme.isoOfGroupIso d.torusIso
    have hroot : d.rootEquiv.weightMap (M.rootDatum.root t) = M.rootDatum.root s := by
      rw [RootPairing.Hom.root_weightMap_apply]
      change M.rootDatum.root
        (d.rootEquiv.indexEquiv (d.rootEquiv.indexEquiv.symm s)) = M.rootDatum.root s
      rw [Equiv.apply_symm_apply]
    have hc := d.exponentCharacter_comp (M.rootDatum.root t)
    rw [hroot] at hc
    have hχ : characterLattice.congr τ
        (splitTorus.exponentCharacter M.base M.coordinates (M.rootDatum.root s)) =
      splitTorus.exponentCharacter M.base M.coordinates (M.rootDatum.root t) := by
      change τ.inv ≫ _ = _
      rw [← hc, ← Category.assoc]
      change (τ.inv ≫ τ.hom) ≫ _ = _
      rw [Iso.inv_hom_id, Category.id_comp]
    obtain ⟨c, hvec, _⟩ := splitTorus.existsUnique_unit_smul_of_aligned_weightLines
      τ d.groupIso d.square (M.rootDatum.root s) (M.rootDatum.root t) hχ
      (M.pinning s) (M.pinning t)
    exact pinning_vector_eq_of_localPinning_of_scalar d.groupIso hpin hvec

/-- Construct an actual pinned automorphism, together with its exact pinning
certificate, from global coordinate alignment and concrete local pinning. -/
def pinnedAutomorphismOfBasedCoordinateIso
    (d : BasedCoordinateIso M.inclusion M.inclusion
      M.rootDatum M.rootDatum M.basis M.basis)
    (hpin : PreservesLocalPinning ((baseChange (𝟙 M.base)).mapIso d.groupIso)) :
    {σ : CategoryTheory.Aut M.group // M.IsPinnedAutomorphism σ d.rootEquiv⁻¹} :=
  ⟨d.groupIso, M.isPinnedAutomorphism_of_basedCoordinateIso d hpin⟩

/-- On a nonempty affine base the label of an exact pinned automorphism is
determined by the actual automorphism. -/
theorem IsPinnedAutomorphism.label_unique [Nonempty M.base]
    {σ : CategoryTheory.Aut M.group} {θ ψ : RootPairing.Aut M.rootDatum}
    (hθ : M.IsPinnedAutomorphism σ θ) (hψ : M.IsPinnedAutomorphism σ ψ) :
    θ = ψ := by
  obtain ⟨_, ⟨τ, hτ, hτχ⟩, _⟩ := hθ
  obtain ⟨_, ⟨ρ, hρ, hρχ⟩, _⟩ := hψ
  let : IsClosedImmersion M.inclusion.hom.hom.left := M.closed
  let : Mono M.inclusion.hom.hom := Over.mono_of_mono_left _
  have ht : τ.hom = ρ.hom := by
    apply hom_ext_points
    intro U x
    apply (cancel_mono M.inclusion.hom.hom).mp
    have h := congrArg (fun a => x ≫ a.hom.hom) (hτ.symm.trans hρ)
    simpa only [Grp.comp_hom_hom, Category.assoc] using h
  have heq (m : M.coordinates → ℤ) :
      splitTorus.exponentCharacter M.base M.coordinates (θ.weightMap m) =
        splitTorus.exponentCharacter M.base M.coordinates (ψ.weightMap m) := by
    have hactual (label : RootPairing.Aut M.rootDatum)
        (hlabel : ∀ (U : Over M.base)
          (x : U ⟶ (splitTorus M.base M.coordinates).X) (m : M.coordinates → ℤ),
          ∏ j, splitTorus.pointsEquiv M.coordinates U (x ≫ τ.hom.hom.hom) j ^
            label.weightMap m j =
              ∏ j, splitTorus.pointsEquiv M.coordinates U x j ^ m j) :
        τ.hom ≫ CommGroupScheme.groupHom
            (splitTorus.exponentCharacter M.base M.coordinates (label.weightMap m)) =
          CommGroupScheme.groupHom (splitTorus.exponentCharacter M.base M.coordinates m) := by
      apply hom_ext_points
      intro U x
      apply (Gm.pointsEquiv M.base U).injective
      simpa only [Grp.comp_hom_hom, ← Category.assoc,
        splitTorus.pointsEquiv_exponentCharacter] using hlabel U x m
    have hψχ : ∀ (U : Over M.base)
        (x : U ⟶ (splitTorus M.base M.coordinates).X) (m : M.coordinates → ℤ),
        ∏ j, splitTorus.pointsEquiv M.coordinates U (x ≫ τ.hom.hom.hom) j ^
          ψ.weightMap m j =
            ∏ j, splitTorus.pointsEquiv M.coordinates U x j ^ m j := by
      simpa only [ht] using hρχ
    have h := (cancel_epi τ.hom).mp
      ((hactual θ hτχ).trans (hactual ψ hψχ).symm)
    exact congrArg Additive.ofMul h
  let x : M.base := Classical.choice inferInstance
  apply StarActionIndependence.equiv_ext_of_weightMap
  intro m
  exact splitTorus.exponentCharacter_injective_of_field_point M.coordinates
    (M.base.fromSpecResidueField x) (heq m)

/-- The identity actual automorphism can only have the identity exact pinned
label on a nonempty affine base. -/
theorem IsPinnedAutomorphism.label_eq_one_of_eq_one [Nonempty M.base]
    {σ : CategoryTheory.Aut M.group} {θ : RootPairing.Aut M.rootDatum}
    (h : M.IsPinnedAutomorphism σ θ) (hσ : σ = 1) : θ = 1 := by
  subst σ
  exact h.label_unique M M.isPinnedAutomorphism_one

end AffinePinnedModel

end Langlands.GroupScheme
