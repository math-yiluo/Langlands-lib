import Langlands.GroupScheme.Torus.SurjectionIsogenySectionStatement
import Langlands.GroupScheme.Torus.FiniteGaloisCharacterDescent
import Langlands.GroupScheme.Torus.CommonFiniteGaloisSplitting
import Langlands.GroupScheme.Torus.GaloisCharacterFunctor
import Langlands.GroupScheme.Torus.Integral
import Langlands.GroupScheme.Torus.SplitLatticeBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-! # Isogeny sections of surjections of tori: proof -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

namespace TorusSurjectionIsogenySection

/-! ### Integral retractions of lattice embeddings -/

section Algebra

open Matrix

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]

/-- An injective map of finite free `ℤ`-modules has a left inverse up to a nonzero integer.
With `A` the matrix of the map, the adjugate of the Gram matrix `Aᵀ A` gives one, the integer
being `det (Aᵀ A)`. -/
theorem exists_leftInverse_zsmul_of_injective
    [Module.Free ℤ M] [Module.Finite ℤ M] [Module.Free ℤ N] [Module.Finite ℤ N]
    (i : M →ₗ[ℤ] N) (hi : Function.Injective i) :
    ∃ m : ℤ, m ≠ 0 ∧ ∃ r : N →ₗ[ℤ] M, ∀ x, r (i x) = m • x := by
  classical
  set bM := Module.Free.chooseBasis ℤ M
  set bN := Module.Free.chooseBasis ℤ N
  set A := LinearMap.toMatrix bM bN i with hAdef
  set G := A.transpose * A with hGdef
  have hA : ∀ v, A *ᵥ v = 0 → v = 0 := by
    intro v hv
    set x := bM.equivFun.symm v with hx
    have hxv : ⇑(bM.repr x) = v := by
      rw [← Module.Basis.equivFun_apply, hx, LinearEquiv.apply_symm_apply]
    have key : A *ᵥ ⇑(bM.repr x) = ⇑(bN.repr (i x)) :=
      LinearMap.toMatrix_mulVec_repr bM bN i x
    rw [hxv, hv] at key
    have hix : bN.repr (i x) = 0 := Finsupp.ext fun j => by simpa using (congrFun key j).symm
    have h0 : x = 0 := hi (by rw [map_zero]; exact bN.repr.injective (by rw [hix, map_zero]))
    simpa [h0] using hxv.symm
  have hG : G.det ≠ 0 := by
    intro h
    obtain ⟨v, hv, hGv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
    apply hv
    apply hA
    rw [← dotProduct_self_eq_zero]
    calc (A *ᵥ v) ⬝ᵥ (A *ᵥ v) = v ⬝ᵥ (G *ᵥ v) := by
          rw [hGdef, ← Matrix.mulVec_mulVec, Matrix.dotProduct_transpose_mulVec]
      _ = 0 := by rw [hGv, dotProduct_zero]
  refine ⟨G.det, hG, Matrix.toLin bN bM (G.adjugate * A.transpose), fun x => ?_⟩
  have hcomp : Matrix.toLin bN bM (G.adjugate * A.transpose) ∘ₗ i =
      G.det • LinearMap.id := by
    conv_lhs => rw [← Matrix.toLin_toMatrix bM bN i, ← hAdef]
    rw [← Matrix.toLin_mul, Matrix.mul_assoc, ← hGdef, Matrix.adjugate_mul,
      LinearEquiv.map_smul, Matrix.toLin_one]
  simpa using LinearMap.congr_fun hcomp x

/-- Averaging a left inverse up to `m` over a finite group gives an equivariant left inverse
up to `|G| m`. -/
theorem exists_equivariant_leftInverse_of_leftInverse
    {G : Type*} [Group G] [Fintype G]
    (ρM : Representation ℤ G M) (ρN : Representation ℤ G N)
    (i : M →ₗ[ℤ] N) (hi : ∀ g x, i (ρM g x) = ρN g (i x))
    (r₀ : N →ₗ[ℤ] M) (m : ℤ) (hr₀ : ∀ x, r₀ (i x) = m • x) :
    ∃ r : N →ₗ[ℤ] M, (∀ g y, r (ρN g y) = ρM g (r y)) ∧
      ∀ x, r (i x) = ((Fintype.card G : ℤ) * m) • x := by
  refine ⟨∑ g : G, ρM g ∘ₗ r₀ ∘ₗ ρN g⁻¹, fun h y => ?_, fun x => ?_⟩
  · simp only [LinearMap.sum_apply, LinearMap.comp_apply, map_sum]
    rw [← Equiv.sum_comp (Equiv.mulLeft h)]
    refine Finset.sum_congr rfl fun g _ => ?_
    simp only [Equiv.coe_mulLeft, _root_.mul_inv_rev, map_mul, Module.End.mul_apply,
      Representation.inv_self_apply]
  · simp only [LinearMap.sum_apply, LinearMap.comp_apply]
    calc ∑ g : G, ρM g (r₀ (ρN g⁻¹ (i x))) = ∑ _g : G, m • x := by
          refine Finset.sum_congr rfl fun g _ => ?_
          rw [← hi, hr₀, map_zsmul, Representation.self_inv_apply]
      _ = ((Fintype.card G : ℤ) * m) • x := by
          rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℤ, smul_smul]

/-- An injective equivariant map of finite free `ℤ`-representations of a finite group has an
equivariant left inverse up to a positive integer. -/
theorem exists_equivariant_retraction
    {G : Type*} [Group G] [Fintype G]
    [Module.Free ℤ M] [Module.Finite ℤ M] [Module.Free ℤ N] [Module.Finite ℤ N]
    (ρM : Representation ℤ G M) (ρN : Representation ℤ G N)
    (i : M →ₗ[ℤ] N) (hinj : Function.Injective i) (hi : ∀ g x, i (ρM g x) = ρN g (i x)) :
    ∃ n : ℕ, 0 < n ∧ ∃ r : N →ₗ[ℤ] M, (∀ g y, r (ρN g y) = ρM g (r y)) ∧
      ∀ x, r (i x) = (n : ℤ) • x := by
  obtain ⟨m, hm, r₀, hr₀⟩ := exists_leftInverse_zsmul_of_injective i hinj
  obtain ⟨r, hr, hri⟩ := exists_equivariant_leftInverse_of_leftInverse ρM ρN i hi r₀ m hr₀
  set d : ℤ := (Fintype.card G : ℤ) * m with hd
  have hd0 : d ≠ 0 := mul_ne_zero (by exact_mod_cast Fintype.card_ne_zero) hm
  refine ⟨d.natAbs * d.natAbs, Nat.mul_pos (Int.natAbs_pos.mpr hd0) (Int.natAbs_pos.mpr hd0),
    d • r, fun g y => ?_, fun x => ?_⟩
  · rw [LinearMap.smul_apply, LinearMap.smul_apply, hr, map_zsmul]
  · rw [LinearMap.smul_apply, hri, smul_smul, Int.natAbs_mul_self]

end Algebra

/-! ### Characters of split tori and surjective homomorphisms -/

section Geometry

/-- The characters of a split torus over a field form a finite free `ℤ`-module. -/
theorem characterLattice_free_finite {K : Type u} [Field K]
    {T : CommGroupScheme (Spec (CommRingCat.of K))} (hT : IsSplitTorus T.toGrp) :
    Module.Free ℤ (characterLattice T) ∧ Module.Finite ℤ (characterLattice T) := by
  obtain ⟨J, hJ, ⟨eT⟩⟩ := hT
  let cT : characterLattice T ≃+ (J → ℤ) :=
    (characterLattice.congr (CommGroupScheme.isoOfGroupIso eT)).trans
      (splitTorus.characterLatticeEquiv K J)
  exact ⟨Module.Free.of_equiv cT.symm.toIntLinearEquiv,
    Module.Finite.equiv cT.symm.toIntLinearEquiv⟩

/-- Pullback of characters along a homomorphism of commutative group schemes over a field
whose underlying scheme morphism is surjective is injective when the target is reduced. -/
theorem pullback_injective_of_surjective {K : Type u} [Field K]
    {T T' : CommGroupScheme (Spec (CommRingCat.of K))}
    [IsReduced T'.X.left] (f : T ⟶ T') [Surjective (CommGroupScheme.hom f)] :
    Function.Injective (characterLattice.pullback f) := by
  have : IsAffineHom (Gm (Spec (CommRingCat.of K))).X.hom := isSplitTorus_gm.isAffineHom
  rw [injective_iff_map_eq_zero]
  intro ψ hψ
  rw [characterLattice.pullback_apply] at hψ
  have hleft : CommGroupScheme.hom ψ = CommGroupScheme.hom (0 : characterLattice T') :=
    ext_of_isDominant_of_isSeparated (Gm (Spec (CommRingCat.of K))).X.hom
      ((Over.w (CommGroupScheme.groupHom ψ).hom.hom).trans
        (Over.w (CommGroupScheme.groupHom (0 : characterLattice T')).hom.hom).symm)
      (CommGroupScheme.hom f)
      (by rw [← CommGroupScheme.hom_comp, ← CommGroupScheme.hom_comp, hψ,
        Limits.comp_zero])
  have hhom : CommGroupScheme.groupHom ψ =
      CommGroupScheme.groupHom (0 : characterLattice T') := by
    apply Grp.hom_ext
    exact Over.OverMorphism.ext hleft
  exact congrArg Additive.ofMul hhom

end Geometry

/-- Base change of an integer multiple of the identity is the same multiple of the identity. -/
theorem baseChange_map_zsmul_id {S S' : Scheme.{u}} (b : S' ⟶ S) (C : CommGroupScheme S)
    (n : ℤ) :
    (CommGroupScheme.baseChange b).map (n • 𝟙 C) =
      n • 𝟙 ((CommGroupScheme.baseChange b).obj C) := by
  change Additive.ofMul ((GroupScheme.baseChange b).map (multiplication C.toGrp n)) =
    Additive.ofMul (multiplication ((CommGroupScheme.baseChange b).obj C).toGrp n)
  exact congrArg Additive.ofMul (multiplication_baseChange b C.toGrp n)

end TorusSurjectionIsogenySection

open TorusSurjectionIsogenySection in
/-- **Isogeny sections of surjections of tori.** For a homomorphism `q : B → C` of
commutative tori over a field whose underlying scheme morphism is surjective, some
homomorphism `s : C → B` satisfies `s ≫ q = [n]` for a positive integer `n`. -/
theorem torusSurjectionIsogenySection : TorusSurjectionIsogenySectionStatement.{u} := by
  intro k _ B C hB hC q hq
  classical
  let d := hB.commonFiniteGaloisSplitting hC
  let L := d.carrier
  let bc := CommGroupScheme.baseChange (algebraBaseMap k L)
  have hBL : IsSplitTorus (bc.obj B).toGrp := d.split_left
  have hCL : IsSplitTorus (bc.obj C).toGrp := d.split_right
  let q' : B ⟶ C := Additive.ofMul q
  let i : characterLattice (bc.obj C) →ₗ[ℤ] characterLattice (bc.obj B) :=
    characterLattice.pullback (bc.map q')
  have hi : ∀ (σ : L ≃ₐ[k] L) (χ : characterLattice (bc.obj C)),
      i (characterLattice.galoisRepresentation k L C σ χ) =
        characterLattice.galoisRepresentation k L B σ (i χ) := fun σ χ =>
    (characterLattice.galoisRepresentation_naturality k L q' σ χ).symm
  have : IsIntegral (bc.obj C).X.left := hCL.isIntegral
  have : Surjective (CommGroupScheme.hom (bc.map q')) :=
    MorphismProperty.overPullbackMap (P := @Surjective) (algebraBaseMap k L) q.hom.hom hq
  have hinj : Function.Injective i := pullback_injective_of_surjective (bc.map q')
  obtain ⟨_, _⟩ := characterLattice_free_finite hBL
  obtain ⟨_, _⟩ := characterLattice_free_finite hCL
  let := Fintype.ofFinite (L ≃ₐ[k] L)
  obtain ⟨n, hn, r, hr, hri⟩ := exists_equivariant_retraction
    (characterLattice.galoisRepresentation k L C) (characterLattice.galoisRepresentation k L B)
    i hinj hi
  obtain ⟨s', hs', -⟩ := hBL.existsUnique_hom_of_equivariant_characterMap (T := C)
    r.toAddMonoidHom (fun σ χ => hr σ χ)
  refine ⟨n, hn, CommGroupScheme.groupHom s', ?_⟩
  have key : s' ≫ q' = (n : ℤ) • 𝟙 C := by
    obtain ⟨a, -, huniq⟩ := hCL.existsUnique_hom_of_equivariant_characterMap (T := C)
      ((n : ℤ) • AddMonoidHom.id _) (fun σ χ => by simp)
    have h1 : s' ≫ q' = a := huniq (s' ≫ q') (fun χ => by
      rw [Functor.map_comp, Category.assoc]
      exact (hs' (i χ)).trans (hri χ))
    have h2 : (n : ℤ) • 𝟙 C = a := huniq ((n : ℤ) • 𝟙 C) (fun χ => by
      rw [baseChange_map_zsmul_id, Preadditive.zsmul_comp, Category.id_comp]
      rfl)
    rw [h1, h2]
  change CommGroupScheme.groupHom (s' ≫ q') = _
  rw [key]
  rfl

end Langlands.GroupScheme
