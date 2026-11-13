import Langlands.GroupScheme.OrthogonalMatrix.Reductive
import Langlands.GroupScheme.Reductive.RootDatumExistence
import Langlands.GroupScheme.Reductive.SplitSemisimplicity
import Langlands.GroupScheme.Reductive.AbsolutelyAlmostSimple
import Langlands.GroupScheme.SimplyConnected.AlmostSimpleFactorDescentProperties
import Langlands.GroupScheme.SimplyConnected.AlmostSimpleFactorGaloisAction

/-! # The identity component of the split orthogonal group is semisimple

Over every field `k` and for `l` with at least two elements, the identity component of the
split orthogonal group `OrthogonalMatrix.groupScheme l k` is semisimple: it is connected
reductive, and its roots `±e_a ± e_b` span a subgroup of the character lattice containing
`2 X`, hence of finite index. It is also nontrivial. Finally, almost simplicity over all
algebraically closed fields gives absolute almost simplicity over every field.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Matrix
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.OrthogonalMatrix

open SymplecticMatrix (weightCoord weightCoord_inl weightCoord_inr)

variable {l : Type} [Fintype l] [DecidableEq l]

section Field

variable {k : Type u} [Field k]

local notation "𝐆" => groupScheme l (CommRingCat.of k)
local notation "𝔻" => splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift l)

/-- Twice every character of the diagonal torus lies in the span of its roots. -/
theorem two_smul_mem_span_roots [Nontrivial l] (χ : characterLattice 𝔻) :
    2 • χ ∈ Submodule.span ℤ (roots (diagonalTorus l (CommRingCat.of k))) := by
  set S := Submodule.span ℤ (roots (diagonalTorus l (CommRingCat.of k)))
  let φ := GeneralLinear.characterCoordEquiv l k
  have hroot : ∀ x y : l ⊕ l, index x ≠ index y →
      φ.symm (weightCoord l x - weightCoord l y) ∈ S := fun x y hxy =>
    Submodule.subset_span ((mem_roots_iff _).2 ⟨x, y, hxy, φ.apply_symm_apply _⟩)
  have hbasis : ∀ a, 2 • φ.symm (Pi.single a 1) ∈ S := by
    intro a
    obtain ⟨b, hba⟩ := exists_ne a
    have e : 2 • φ.symm (Pi.single a 1) =
        φ.symm (weightCoord l (Sum.inl a) - weightCoord l (Sum.inl b)) +
          φ.symm (weightCoord l (Sum.inl a) - weightCoord l (Sum.inr b)) := by
      rw [← map_add, ← map_nsmul]
      congr 1
      rw [weightCoord_inl, weightCoord_inl, weightCoord_inr]
      funext c
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.single_apply]
      split_ifs <;> simp
    rw [e]
    exact S.add_mem (hroot _ _ (by simpa using Ne.symm hba))
      (hroot _ _ (by simpa using Ne.symm hba))
  have hle : (⊤ : Submodule ℤ (characterLattice 𝔻)) ≤ S.comap (2 • LinearMap.id) := by
    rw [← ((Pi.basisFun ℤ l).map φ.symm).span_eq, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    rw [Module.Basis.map_apply, Pi.basisFun_apply, SetLike.mem_coe, Submodule.mem_comap,
      LinearMap.smul_apply, LinearMap.id_apply]
    exact hbasis a
  have h := hle (Submodule.mem_top (x := χ))
  rwa [Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply] at h

/-- The roots of the diagonal torus span a subgroup of finite index of the character lattice,
for every root datum whose roots are those roots. -/
theorem finite_quotient_rootSpan [Nontrivial l] {J : Type*}
    (P : RootDatum J (characterLattice 𝔻) (cocharacterLattice 𝔻))
    (hP : Set.range P.root = roots (diagonalTorus l (CommRingCat.of k))) :
    Finite (characterLattice 𝔻 ⧸ P.rootSpan ℤ) := by
  have h2 : ∀ χ : characterLattice 𝔻, 2 • χ ∈ P.rootSpan ℤ := fun χ => by
    have h := two_smul_mem_span_roots (k := k) χ
    rw [← hP] at h
    exact h
  let φ := GeneralLinear.characterCoordEquiv l k
  let f : (l → ZMod 2) → characterLattice 𝔻 ⧸ P.rootSpan ℤ :=
    fun n => Submodule.Quotient.mk (φ.symm fun a => ((n a).val : ℤ))
  refine Finite.of_surjective f fun q => ?_
  obtain ⟨χ, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  refine ⟨fun a => (φ χ a : ZMod 2), (Submodule.Quotient.eq _).2 ?_⟩
  have e : φ.symm (fun a => (((φ χ a : ZMod 2)).val : ℤ)) - χ =
      2 • φ.symm (fun a => -(φ χ a / 2)) := by
    apply φ.injective
    rw [map_sub, map_nsmul, φ.apply_symm_apply, φ.apply_symm_apply]
    funext a
    simp only [Pi.sub_apply, Pi.smul_apply, ZMod.val_intCast]
    rw [nsmul_eq_mul]
    push_cast
    omega
  rw [e]
  exact h2 _

variable (l k)

/-- **Semisimplicity.** The identity component of the split orthogonal group over a field is
semisimple, when `l` has at least two elements. -/
theorem isSemisimple_identityComponent [Nontrivial l] :
    IsSemisimple (identityComponent 𝐆) := by
  have hRed := isConnectedReductive_identityComponent l k
  obtain ⟨J, _, P, hP, -⟩ := rootDatumExistence k _ hRed 𝔻
    (SymplecticMatrix.isSplitTorus_diagonalTorus l k) (identityTorus l k)
    (isMaximalTorus_identityTorus l k)
  refine ((splitSemisimpleRootDatum k _ hRed 𝔻 (SymplecticMatrix.isSplitTorus_diagonalTorus l k)
    (identityTorus l k) (isMaximalTorus_identityTorus l k) J P hP).1).2 ?_
  exact finite_quotient_rootSpan P (hP.2.1.trans (roots_identityTorus l k))

/-- **Nontriviality.** The identity component of the split orthogonal group over a field is
nontrivial, when `l` has at least two elements: it contains the constant point of
`upper(E_ab - E_ba)`. -/
theorem range_id_identityComponent_ne_bot [Nontrivial l] :
    SubgroupFunctor.range (𝟙 (identityComponent 𝐆)) ≠ ⊥ := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne l
  intro hbot
  let T₀ : Over (Spec (CommRingCat.of k)) := Over.mk (𝟙 (Spec (CommRingCat.of k)))
  obtain ⟨c, hc⟩ := SubgroupFunctor.mem_range.1
    (constantPoint_upper_mem T₀ (isAlt_alt (K := k) a b))
  have hc1 : c ∈ (SubgroupFunctor.range (𝟙 (identityComponent 𝐆))).carrier T₀ :=
    SubgroupFunctor.mem_range.2 ⟨c, Category.comp_id c⟩
  rw [hbot, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hc1
  rw [hc1, MonObj.one_comp] at hc
  have h1 := congrArg (fun y => ((pointsEquiv l _ T₀ y : orthogonalGroup l _) :
    Matrix (l ⊕ l) (l ⊕ l) Γ(T₀.left, ⊤)) (Sum.inl a) (Sum.inr b)) hc
  simp only [pointsEquiv_constantPoint, map_one, coe_map] at h1
  have h2 : (0 : Γ(T₀.left, ⊤)) = 1 := by
    simpa [SymplecticMatrix.upper, alt, hab] using h1
  let e : k ≃+* Γ(T₀.left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
  exact one_ne_zero (e.injective (by rw [map_one, map_zero, h2]))

end Field

variable (l)

/-- Almost simplicity of the identity components of the split orthogonal groups over all
algebraically closed fields gives absolute almost simplicity over every field. -/
theorem isAbsolutelyAlmostSimple_of_isAlmostSimple
    (h : ∀ (k : Type u) [Field k] [IsAlgClosed k],
      IsAlmostSimple (identityComponent (groupScheme l (CommRingCat.of k))))
    (K : Type u) [Field K] :
    IsAbsolutelyAlmostSimple (identityComponent (groupScheme l (CommRingCat.of K))) := by
  have hbar : IsAlmostSimple ((GroupScheme.baseChange (toAlgebraicClosure K)).obj
      (identityComponent (groupScheme l (CommRingCat.of K)))) :=
    IsAlmostSimple.of_iso
      (IdentityComponent.baseChangeIso (groupScheme l (CommRingCat.of K))
          (algebraMap K (AlgebraicClosure K)) ≪≫
        IdentityComponent.mapIso (baseChangeModelIso l (toAlgebraicClosure K)))
      (h (AlgebraicClosure K))
  exact ⟨IsAlmostSimple.of_fieldExtension (K := AlgebraicClosure K) hbar, hbar⟩

end Langlands.GroupScheme.OrthogonalMatrix
