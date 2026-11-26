import Langlands.GroupScheme.Lie.SmoothAdjointKernelCenterQuotientStatement
import Langlands.GroupScheme.IdentityJetAffineChart
import Langlands.GroupScheme.IdentityJetCentralizerComparison
import Langlands.GroupScheme.IdentityJetRepresentation
import Langlands.GroupScheme.GeometricConnectedness
import Langlands.GroupScheme.AffineHomImageProof
import Langlands.GroupScheme.Absolute.SolvableUnipotentAdapters
import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.GroupScheme.UnipotentClosedSubgroupProof
import Langlands.GroupScheme.UnitriangularUnipotentProof
import Langlands.GroupScheme.Dynamic.UnitriangularEmbedding
import Langlands.GroupScheme.Reductive.CharZeroSemisimplicity.FlagBasis
import Langlands.RingTheory.TensorProduct.QuotientKernel

/-! # Unipotence of the adjoint kernel modulo the full centre -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Langlands.AlgebraicGeometry.AffinePoints
open scoped CategoryTheory.MonObj TensorProduct Matrix

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Lie

open IdentityJet

variable {k : Type u} [Field k]

private theorem exists_augmentedJet (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [Smooth G.X.hom] (n : ℕ) :
    ∃ (P : Type u) (_ : CommRing P) (_ : Algebra k P)
      (e : IdentityJet.scheme G n ≅ Spec (CommRingCat.of P))
      (he : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k P)) = projection G n)
      (ε : P →ₐ[k] k),
      Module.Finite k P ∧ RingHom.ker ε ^ (n + 1) = ⊥ ∧ jetPoint G n e he ε = 1 := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let V : G.X.left.affineOpens := ⟨⊤, isAffineOpen_top _⟩
  have hV : G.identitySection ⁻¹ᵁ V.1 = ⊤ := rfl
  let : Algebra k Γ(G.X.left, V.1) := (chartRingHom G V).toAlgebra
  let P := chartJetAlgebra G n V
  let e := chartJetIso G n V hV
  have he := chartJetIso_projection G n V hV
  let ε₀ : Γ(G.X.left, V.1) →ₐ[k] k :=
    { chartAugmentation G V hV with
      commutes' := chartAugmentation_chartRingHom G V hV }
  have hI : (ideal G n).ideal V = RingHom.ker ε₀ ^ (n + 1) :=
    ideal_eq_ker_chartAugmentation_pow G n V hV
  have hle : (ideal G n).ideal V ≤ RingHom.ker ε₀ :=
    hI ▸ Ideal.pow_le_self (Nat.succ_ne_zero n)
  let ε : P →ₐ[k] k := Ideal.Quotient.liftₐ _ ε₀ (fun _ hx => RingHom.mem_ker.mp (hle hx))
  refine ⟨P, inferInstance, inferInstance, e, he, ε,
    (chartJetAlgebra_finite_projective G n V hV).1, ?_, ?_⟩
  · change RingHom.ker (Ideal.Quotient.lift _ ε₀.toRingHom hle) ^ (n + 1) = ⊥
    change (ideal G n).ideal V = RingHom.ker ε₀.toRingHom ^ (n + 1) at hI
    rw [Ideal.ker_quotient_lift, ← Ideal.map_pow, ← hI, Ideal.map_quotient_self]
  · apply Over.OverMorphism.ext
    rw [jetPoint_left]
    change Spec.map (CommRingCat.ofHom ε.toRingHom) ≫
      (affineChartIso G n V hV).inv ≫ inclusion G n = _
    rw [affineChartIso_inv_inclusion, ← Spec.map_comp_assoc,
      ← CommRingCat.ofHom_comp, IsAffineOpen.fromSpec_top]
    have hε : ε.toRingHom.comp (Ideal.Quotient.mk ((ideal G n).ideal V)) = ε₀ := rfl
    rw [hε]
    change Spec.map (G.identitySection.appLE ⊤ ⊤ hV.ge ≫ (Scheme.ΓSpecIso _).hom) ≫
      G.X.left.isoSpec.inv = _
    have happ : G.identitySection.appLE ⊤ ⊤ hV.ge = G.identitySection.appTop := by
      simp [Scheme.Hom.appLE]
    rw [happ, Spec.map_comp, ← Scheme.isoSpec_Spec_hom,
      Category.assoc, Scheme.isoSpec_inv_naturality, Iso.hom_inv_id_assoc]
    change G.identitySection = Spec.map (CommRingCat.ofHom (algebraMap k k)) ≫ G.identitySection
    simp

private theorem adjoint_fixes_dualNumber {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] {d : ℕ} (c : FiniteCoordinates G d)
    {A : Type u} [CommRing A] [Algebra k A] (g : specOver (R := k) A ⟶ G.X)
    (hg : g ≫ (adjointRepresentation c).hom.hom = 1) (x : lieKernel G A) :
    constant G g * x.val * (constant G g)⁻¹ = x.val := by
  let B := CommAlgCat.of (CommRingCat.of k) A
  have hx := adjointRepresentation_affineAction c B g (Additive.ofMul x)
  have hM : (adjointRepresentation c).affineMatrix B g = 1 := by
    rw [MatrixRepresentation.affineMatrix_apply, hg, map_one]
  rw [MatrixRepresentation.affineAction_apply, hM, Units.val_one, Matrix.one_mulVec] at hx
  have hx' := (c.equiv B).injective hx.symm
  exact congrArg (fun y : Additive (lieKernel G A) => y.toMul.val) hx'

section Cotangent

variable {P A : Type u} [CommRing P] [Algebra k P] [CommRing A] [Algebra k A]

private def tensorAugmentation (ε : P →ₐ[k] k) : (A ⊗[k] P) →ₐ[k] A :=
  (Algebra.TensorProduct.rid k k A).toAlgHom.comp
    (Algebra.TensorProduct.map (AlgHom.id k A) ε)

private theorem tensorAugmentation_ker (ε : P →ₐ[k] k) :
    RingHom.ker (tensorAugmentation (A := A) ε) =
      Ideal.rightTensorIdeal k A (RingHom.ker ε) := by
  change RingHom.ker ((Algebra.TensorProduct.rid k k A).toRingEquiv.toRingHom.comp
    (Algebra.TensorProduct.map (AlgHom.id k A) ε).toRingHom) = _
  rw [RingHom.ker_comp_of_injective _
    (f := (Algebra.TensorProduct.rid k k A).toRingEquiv.toRingHom)
    (Algebra.TensorProduct.rid k k A).injective]
  exact Algebra.TensorProduct.lTensor_ker ε
    (fun r => ⟨algebraMap k P r, ε.commutes r⟩)

private theorem tensorAugmentation_left (ε : P →ₐ[k] k) :
    (tensorAugmentation (A := A) ε).comp Algebra.TensorProduct.includeLeft = AlgHom.id k A := by
  ext a
  simp [tensorAugmentation, Algebra.TensorProduct.rid_tmul]

private theorem tensorAugmentation_right (ε : P →ₐ[k] k) :
    (tensorAugmentation (A := A) ε).comp Algebra.TensorProduct.includeRight =
      (Algebra.ofId k A).comp ε := by
  ext p
  simp [tensorAugmentation, Algebra.TensorProduct.rid_tmul, Algebra.smul_def]

private def squareQuotientTest {C : Type u} [CommRing C] [Algebra k C]
    (J : Ideal C) (s : C →ₐ[k] C) (hs : ∀ x, x - s x ∈ J) :
    C →ₐ[k] DualNumber (C ⧸ J ^ 2) := by
  let q := Ideal.Quotient.mkₐ k (J ^ 2)
  refine
    { toFun := fun x => ⟨q (s x), q (x - s x)⟩
      map_zero' := by apply TrivSqZeroExt.ext <;> simp
      map_one' := by apply TrivSqZeroExt.ext <;> simp
      map_add' := fun x y => by
        apply TrivSqZeroExt.ext
        · simp
        · simp only [TrivSqZeroExt.snd_mk, map_sub, map_add, TrivSqZeroExt.snd_add]
          abel
      map_mul' := fun x y => by
        have h : q (x - s x) * q (y - s y) = 0 := by
          rw [← map_mul]
          apply Ideal.Quotient.eq_zero_iff_mem.mpr
          rw [pow_two]
          exact Ideal.mul_mem_mul (hs x) (hs y)
        apply TrivSqZeroExt.ext
        · simp
        · simp only [map_sub] at h
          simp only [map_sub, map_mul, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_mk,
            TrivSqZeroExt.snd_mk, smul_eq_mul, op_smul_eq_smul]
          linear_combination h
      commutes' := fun x => by
        apply TrivSqZeroExt.ext
        · change q (s (algebraMap k C x)) = _
          rw [s.commutes, q.commutes]
          rfl
        · change q (algebraMap k C x - s (algebraMap k C x)) = _
          rw [s.commutes, sub_self, map_zero]
          rfl }

private theorem conjBeta_fixed_in_dualNumbers {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] {d : ℕ} (c : FiniteCoordinates G d) (n : ℕ)
    (e : IdentityJet.scheme G n ≅ Spec (CommRingCat.of P))
    (he : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k P)) = projection G n)
    (ε : P →ₐ[k] k) (hε : jetPoint G n e he ε = 1)
    (g : specOver (R := k) A ⟶ G.X) (hg : g ≫ (adjointRepresentation c).hom.hom = 1)
    {D : Type u} [CommRing D] [Algebra k D] (j : A →ₐ[k] D)
    (ψ : A ⊗[k] P →ₐ[k] DualNumber D)
    (hl : ψ.comp Algebra.TensorProduct.includeLeft = (TrivSqZeroExt.inlAlgHom k D D).comp j)
    (hr : (TrivSqZeroExt.fstHom k D D).comp (ψ.comp Algebra.TensorProduct.includeRight) =
      (Algebra.ofId k D).comp ε) :
    ψ.comp (conjBeta G n e he g) = ψ.comp Algebra.TensorProduct.includeRight := by
  let x : lieKernel G D := ⟨jetPoint G n e he (ψ.comp Algebra.TensorProduct.includeRight), by
    change specMapOver (TrivSqZeroExt.fstHom k D D) ≫ jetPoint G n e he _ = 1
    rw [specMapOver_comp_jetPoint, hr, ← specMapOver_comp_jetPoint, hε, MonObj.comp_one]⟩
  have hgD : (specMapOver j ≫ g) ≫ (adjointRepresentation c).hom.hom = 1 := by
    rw [Category.assoc, hg, MonObj.comp_one]
  have hfix := adjoint_fixes_dualNumber c (specMapOver j ≫ g) hgD x
  apply jetPoint_injective G n e he
  rw [← conj_jetPoint, hl, ← specMapOver_comp_specMapOver, Category.assoc]
  exact hfix

private theorem conjAlg_sub_mem_square {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] {d : ℕ} (c : FiniteCoordinates G d) (n : ℕ)
    (e : IdentityJet.scheme G n ≅ Spec (CommRingCat.of P))
    (he : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k P)) = projection G n)
    (ε : P →ₐ[k] k) (hε : jetPoint G n e he ε = 1)
    (g : specOver (R := k) A ⟶ G.X) (hg : g ≫ (adjointRepresentation c).hom.hom = 1)
    (z : A ⊗[k] P) :
    conjAlg G n e he g z - z ∈ (Ideal.rightTensorIdeal k A (RingHom.ker ε)) ^ 2 := by
  let J := Ideal.rightTensorIdeal k A (RingHom.ker ε)
  let D := (A ⊗[k] P) ⧸ J ^ 2
  let q : (A ⊗[k] P) →ₐ[k] D := Ideal.Quotient.mkₐ k _
  let a : (A ⊗[k] P) →ₐ[k] A := tensorAugmentation ε
  let l : A →ₐ[k] A ⊗[k] P := Algebra.TensorProduct.includeLeft
  let r : P →ₐ[k] A ⊗[k] P := Algebra.TensorProduct.includeRight
  let s := l.comp a
  have ha : a.comp l = AlgHom.id k A := tensorAugmentation_left ε
  have hs (x : A ⊗[k] P) : x - s x ∈ J := by
    change _ ∈ Ideal.rightTensorIdeal k A (RingHom.ker ε)
    rw [← tensorAugmentation_ker]
    change a (x - l (a x)) = 0
    rw [map_sub, show a (l (a x)) = a x from DFunLike.congr_fun ha (a x), sub_self]
  let ψ : (A ⊗[k] P) →ₐ[k] DualNumber D := squareQuotientTest J s hs
  have hψl : ψ.comp l = (TrivSqZeroExt.inlAlgHom k D D).comp (q.comp l) := by
    apply AlgHom.ext
    intro x
    apply TrivSqZeroExt.ext
    · exact congrArg (fun t => q (l t)) (DFunLike.congr_fun ha x)
    · change q (l x - l (a (l x))) = 0
      rw [show a (l x) = x from DFunLike.congr_fun ha x, sub_self, map_zero]
  have hψr : (TrivSqZeroExt.fstHom k D D).comp (ψ.comp r) = (Algebra.ofId k D).comp ε := by
    ext p
    change q (l (a (r p))) = algebraMap k D (ε p)
    rw [show a (r p) = algebraMap k A (ε p) from
      DFunLike.congr_fun (tensorAugmentation_right (A := A) ε) p, AlgHom.commutes,
      AlgHom.commutes]
  have hβ : ψ.comp (conjBeta G n e he g) = ψ.comp r :=
    conjBeta_fixed_in_dualNumbers c n e he ε hε g hg (q.comp l) ψ hψl hψr
  have hψ : ψ.comp ((conjAlg G n e he g).restrictScalars k) = ψ := by
    apply Algebra.TensorProduct.ext
    · rw [AlgHom.comp_assoc, conjAlg_comp_includeLeft]
    · change (ψ.comp ((conjAlg G n e he g).restrictScalars k)).comp r = ψ.comp r
      rw [AlgHom.comp_assoc, conjAlg_comp_includeRight]
      exact hβ
  have hq (y : A ⊗[k] P) : (ψ y).fst + (ψ y).snd = q y := by
    change q (s y) + q (y - s y) = q y
    rw [← map_add]
    congr 1
    abel
  have hz := congrArg (fun t : DualNumber D => t.fst + t.snd) (DFunLike.congr_fun hψ z)
  change (ψ (conjAlg G n e he g z)).fst + (ψ (conjAlg G n e he g z)).snd =
    (ψ z).fst + (ψ z).snd at hz
  rw [hq, hq] at hz
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change q (_ - _) = 0
  rw [map_sub, hz, sub_self]

end Cotangent

private theorem sub_mem_next_power {C : Type u} [CommRing C] (J : Ideal C)
    (f : C →+* C) (h : ∀ x, f x - x ∈ J ^ 2) :
    ∀ t x, x ∈ J ^ t → f x - x ∈ J ^ (t + 1) := by
  intro t
  induction t with
  | zero =>
    intro x _
    exact Ideal.pow_le_pow_right (by decide : 0 + 1 ≤ 2) (h x)
  | succ t ih =>
    intro x hx
    rw [pow_succ' J t] at hx
    refine Submodule.mul_induction_on hx (fun y hy z hz => ?_) (fun y z hy hz => ?_)
    · have hfy : f y ∈ J := by
        have hd : f y - y ∈ J := Ideal.pow_le_self (by decide : 2 ≠ 0) (h y)
        simpa only [sub_add_cancel] using J.add_mem hd hy
      have h₁ : (f y - y) * z ∈ J ^ (t + 1 + 1) := by
        rw [show t + 1 + 1 = 2 + t by omega, pow_add]
        exact Ideal.mul_mem_mul (h y) hz
      have h₂ : f y * (f z - z) ∈ J ^ (t + 1 + 1) := by
        rw [pow_succ' J (t + 1)]
        exact Ideal.mul_mem_mul hfy (ih z hz)
      rw [map_mul, show f y * f z - y * z = (f y - y) * z + f y * (f z - z) by ring]
      exact Ideal.add_mem _ h₁ h₂
    · rw [map_add, add_sub_add_comm]
      exact Ideal.add_mem _ hy hz

section Filtration

variable {P : Type u} [CommRing P] [Algebra k P]

private theorem exists_basis_idealPowers [Module.Finite k P] (J : Ideal P)
    (n : ℕ) (hJ : J ^ n = ⊥) :
    ∃ (m : ℕ) (b : Module.Basis (Fin m) k P) (w : Fin m → ℕ),
      ∀ t, (J ^ t).restrictScalars k = Submodule.span k (b '' {i | t ≤ w i}) := by
  let e := (Module.finBasis k P).equivFun
  let F (t : ℕ) := ((J ^ t).restrictScalars k).map e.toLinearMap
  have hF : Antitone F := fun _ _ h => Submodule.map_mono (Ideal.pow_le_pow_right h)
  have h0 : F 0 = ⊤ := by
    simp [F, Ideal.one_eq_top, LinearMap.range_eq_top.mpr e.surjective]
  have hn : F n = ⊥ := by simp [F, hJ]
  obtain ⟨b, w, hb⟩ := Langlands.LinearAlgebra.exists_basis_flag F hF h0 n hn
  refine ⟨_, b.map e.symm, w, fun t => ?_⟩
  have hcomp : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by
    ext x
    exact e.symm_apply_apply x
  have h := congrArg (Submodule.map e.symm.toLinearMap) (hb t)
  simpa only [F, ← Submodule.map_comp, hcomp, Submodule.map_id, Submodule.map_span,
    Set.image_image, LinearEquiv.coe_coe, Module.Basis.map_apply, Function.comp_def] using h

variable {A : Type u} [CommRing A] [Algebra k A] {m : ℕ}

private theorem tensorBasis_repr_eq_zero (J : Ideal P) (b : Module.Basis (Fin m) k P)
    (w : Fin m → ℕ)
    (hb : ∀ t, (J ^ t).restrictScalars k = Submodule.span k (b '' {i | t ≤ w i}))
    {t : ℕ} {z : A ⊗[k] P} (hz : z ∈ (Ideal.rightTensorIdeal k A J) ^ t)
    {i : Fin m} (hi : w i < t) :
    (Algebra.TensorProduct.basis A b).repr z i = 0 := by
  have hmap : (Ideal.rightTensorIdeal k A J) ^ t = Ideal.rightTensorIdeal k A (J ^ t) := by
    simp only [Ideal.rightTensorIdeal_def, Ideal.map_pow]
  rw [hmap] at hz
  let l := ((J ^ t).subtype.restrictScalars k).lTensor A
  have hr : z ∈ LinearMap.range l := by
    have h := Ideal.map_includeRight_eq (R := k) (A := A) (J ^ t)
    change (Ideal.rightTensorIdeal k A (J ^ t)).restrictScalars k = LinearMap.range l at h
    rw [← h]
    exact hz
  clear hz
  obtain ⟨v, rfl⟩ := hr
  induction v using TensorProduct.inductionOn with
  | tmul a p =>
    have hp : (p : P) ∈ (J ^ t).restrictScalars k := p.property
    have hpi : b.repr (p : P) i = 0 := by
      rw [hb, Module.Basis.mem_span_image] at hp
      by_contra hne
      exact (not_le_of_gt hi) (hp (Finsupp.mem_support_iff.mpr hne))
    change (Algebra.TensorProduct.basis A b).repr (a ⊗ₜ[k] (p : P)) i = 0
    simp [Algebra.TensorProduct.basis_repr_tmul, hpi]
  | add v v' hv hv' => simp [map_add, hv, hv']

private theorem conjGL_mem_blockUnipotent {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] {d : ℕ} (c : FiniteCoordinates G d) (n : ℕ)
    (e : IdentityJet.scheme G n ≅ Spec (CommRingCat.of P))
    (he : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k P)) = projection G n)
    (ε : P →ₐ[k] k) (hε : jetPoint G n e he ε = 1)
    (b : Module.Basis (Fin m) k P) (w : Fin m → ℕ)
    (hb : ∀ t, (RingHom.ker ε ^ t).restrictScalars k = Submodule.span k (b '' {i | t ≤ w i}))
    (g : specOver (R := k) A ⟶ G.X) (hg : g ≫ (adjointRepresentation c).hom.hom = 1) :
    conjGL G n e he b g ∈ GeneralLinear.blockUnipotentSubgroup A
      (fun i => (w i : ℤ)) := by
  rw [GeneralLinear.mem_blockUnipotentSubgroup]
  intro i j hij
  have hg' : g⁻¹ ≫ (adjointRepresentation c).hom.hom = 1 := by
    rw [GrpObj.inv_comp, hg, inv_one]
  let J := RingHom.ker ε
  have hbj : b j ∈ J ^ (w j) := by
    change b j ∈ (J ^ (w j)).restrictScalars k
    rw [hb]
    exact Submodule.subset_span ⟨j, Set.mem_ofPred_eq.mpr (le_rfl : w j ≤ w j), rfl⟩
  let v := (Algebra.TensorProduct.basis A b) j
  have hv : v ∈ (Ideal.rightTensorIdeal k A J) ^ (w j) := by
    change (Algebra.TensorProduct.basis A b) j ∈ _
    rw [Algebra.TensorProduct.basis_apply, Ideal.rightTensorIdeal_def, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem
      (Algebra.TensorProduct.includeRight : P →ₐ[k] A ⊗[k] P).toRingHom hbj
  let f := conjAlg G n e he g⁻¹
  have hd : f v - v ∈ (Ideal.rightTensorIdeal k A J) ^ (w j + 1) :=
    sub_mem_next_power _ f.toRingHom (conjAlg_sub_mem_square c n e he ε hε g⁻¹ hg') _ _ hv
  have hzero := tensorBasis_repr_eq_zero J b w hb hd (i := i) (by exact_mod_cast
    (show (w i : ℤ) < (w j : ℤ) + 1 by omega))
  apply sub_eq_zero.mp
  rw [show ((conjGL G n e he b g : GL (Fin m) A) : Matrix (Fin m) (Fin m) A) =
    LinearMap.toMatrix (Algebra.TensorProduct.basis A b) (Algebra.TensorProduct.basis A b)
      f.toLinearMap from rfl,
    ← LinearMap.toMatrix_id (Algebra.TensorProduct.basis A b)]
  have hc := hzero
  rw [map_sub, Finsupp.sub_apply] at hc
  simpa only [LinearMap.toMatrix_apply, AlgHom.toLinearMap_apply, LinearMap.id_apply] using hc

end Filtration

private theorem exists_conjugation_representation {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsSeparated G.X.hom] (n : ℕ) {P : Type u} [CommRing P] [Algebra k P]
    (e : IdentityJet.scheme G n ≅ Spec (CommRingCat.of P))
    (he : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k P)) = projection G n)
    {m : ℕ} (b : Module.Basis (Fin m) k P) :
    ∃ ρ : MatrixRepresentation G (Fin m),
      (∀ (A : Type u) [CommRing A] [Algebra k A] (g : specOver (R := k) A ⟶ G.X),
        g ≫ ρ.hom.hom = GeneralLinear.pointOfMatrix (conjGL G n e he b g)) ∧
      (∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X),
        g ≫ ρ.hom.hom = 1 ↔ CentralizesJet G n g) := by
  obtain ⟨f, hf⟩ := exists_conjugationMorphism G n e he b
  have hmul (T : Over (Spec (CommRingCat.of k))) (x y : T ⟶ G.X) :
      (x * y) ≫ f = (x ≫ f) * (y ≫ f) := by
    apply over_hom_ext
    intro A _ _ t
    rw [← Category.assoc, MonObj.comp_mul, MonObj.comp_mul, ← Category.assoc, ← Category.assoc]
    simp only [hf, conjGL_mul, GeneralLinear.pointOfMatrix_mul]
  let φ : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ G.X) →* (T ⟶ (GeneralLinear.groupScheme (Fin m) (CommRingCat.of k)).X) :=
    fun T => MonoidHom.mk' (fun x => x ≫ f) (hmul T)
  let ρ := homOfPoints φ (fun a x => Category.assoc a x f)
  have hρ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X) :
      g ≫ ρ.hom.hom = g ≫ f := comp_homOfPoints _ _ T g
  refine ⟨ρ, fun A _ _ g => (hρ _ g).trans (hf A g), fun T g => ?_⟩
  rw [hρ]
  constructor
  · intro h
    apply centralizesJet_of_affine G n
    intro A _ _ t
    rw [← conjGL_eq_one_iff G n e he b, ← (GeneralLinear.pointOfMatrix_injective
      (R := k) (A := A) (m := m)).eq_iff, ← hf, Category.assoc, h, MonObj.comp_one,
      GeneralLinear.pointOfMatrix_one]
  · intro h
    apply over_hom_ext
    intro A _ _ t
    rw [← Category.assoc, hf, MonObj.comp_one,
      (conjGL_eq_one_iff G n e he b _).mpr (h.comp t), GeneralLinear.pointOfMatrix_one]

private theorem comp_hom_eq_one_iff {S : Scheme.{u}} {G H I : GroupScheme S}
    {T : Over S} (x : T ⟶ G.X) (f : G ⟶ H) (i : H ⟶ I) [Mono i.hom.hom] :
    x ≫ (f ≫ i).hom.hom = 1 ↔ x ≫ f.hom.hom = 1 := by
  rw [Grp.comp_hom_hom, ← Category.assoc, ← MonObj.one_comp i.hom.hom, cancel_mono]

open _root_.Langlands.GroupScheme.GeneralLinear

/-- Milne 14.23 for a smooth connected affine group, with the full scheme kernel
and centre and an actual fppf quotient projection. -/
theorem smoothAdjointKernelCenterQuotient : SmoothAdjointKernelCenterQuotientStatement.{u} := by
  intro k _ G _ _ _ d c
  classical
  let R := CommRingCat.of k
  have : GeometricallyConnected G.X.hom := geometricallyConnected_of_connected G
  obtain ⟨n, hn⟩ := exists_order_detects_center G
  obtain ⟨P, _, _, e, he, ε, hP, hnil, hε⟩ := exists_augmentedJet G n
  obtain ⟨m, b, w, hb⟩ := exists_basis_idealPowers (k := k) (RingHom.ker ε) (n + 1) hnil
  obtain ⟨ρ, hρ, hker⟩ := exists_conjugation_representation n e he b
  let a := adjointRepresentation c
  let N := kernel a
  let j := kernelι a
  have : IsClosedImmersion j.hom.hom.left := kernelι_isClosedImmersion a
  have : IsAffineHom N.X.hom := by
    rw [← Over.w j.hom.hom]
    infer_instance
  have : LocallyOfFiniteType N.X.hom := by
    rw [← Over.w j.hom.hom]
    infer_instance
  let v (i : Fin m) : ℤ := w i
  let σ := reindexIso (antitoneEnumeration v).symm R
  let t (i : Fin (Fintype.card (Fin m))) : ℤ := -(i.val : ℤ)
  let f := (j ≫ ρ) ≫ σ.hom
  let U := blockUnipotentScheme (Fin (Fintype.card (Fin m))) R t
  let iU := blockUnipotentHom (Fin (Fintype.card (Fin m))) R t
  let F := blockUnipotent (Fin (Fintype.card (Fin m))) R t
  have hf : SubgroupFunctor.range f ≤ F := by
    have hA : IsAffine N.X.left := isAffine_of_isAffineHom N.X.hom
    obtain ⟨B, ⟨eN⟩⟩ := (essImage_algSpec (G := N.X)).mpr hA
    let y : specOver (R := k) B.unop ⟶ N.X := eN.hom
    let g := y ≫ j.hom.hom
    have hg : g ≫ a.hom.hom = 1 := (mem_range_kernelι_iff a g).mp ⟨y, rfl⟩
    have hconj := conjGL_mem_blockUnipotent c n e he ε hε b w hb g hg
    have hy : y ≫ f.hom.hom ∈ F.carrier (specOver (R := k) B.unop) := by
      change pointsEquiv _ R _ (y ≫ f.hom.hom) ∈ blockUnipotentSubgroup _ t
      simp only [f, Grp.comp_hom_hom, ← Category.assoc]
      rw [pointsEquiv_reindexIso, hρ, pointOfMatrix, MulEquiv.apply_symm_apply]
      exact matrixReindex_mem_unitriangular _ v _
        (map_mem_blockUnipotentSubgroup v _ hconj)
    have hs := F.comp_mem eN.inv hy
    have hid : eN.inv ≫ (y ≫ f.hom.hom) = f.hom.hom := eN.inv_hom_id_assoc _
    rw [hid] at hs
    rintro T _ ⟨x, rfl⟩
    exact F.comp_mem x hs
  let hU := isRepresentedBy_blockUnipotent (Fin (Fintype.card (Fin m))) R t
  let p : N ⟶ U := hU.factorHom f hf
  have hp : p ≫ iU = f := hU.factorHom_comp f hf
  have : IsAffineHom U.X.hom := isAffineHom_blockUnipotentScheme _ R t
  have : LocallyOfFiniteType U.X.hom := locallyOfFiniteType_blockUnipotentScheme _ R t
  obtain ⟨Q, q, i, hQft, hQaff, hi, hqi, hq⟩ := affineHomImage k N U p
  refine ⟨Q, q, hQaff, hQft, ?_, unipotentClosedSubgroup k U Q i hi
    (unitriangularUnipotent k (Fintype.card (Fin m)))⟩
  have : Mono i.hom.hom.left := (IsClosedImmersion.iff_isFinite_and_mono _).mp hi |>.2
  have : Mono i.hom.hom := Over.mono_of_mono_left i.hom.hom
  have : Mono iU.hom.hom := hU.1
  have hfull : SubgroupFunctor.range (kernelι q) = (center G).comap j := by
    apply SubgroupFunctor.ext
    intro T
    apply Subgroup.ext
    intro x
    rw [mem_range_kernelι_iff, ← comp_hom_eq_one_iff x q i, hqi,
      ← comp_hom_eq_one_iff x p iU, hp]
    change x ≫ ((j ≫ ρ) ≫ σ.hom).hom.hom = 1 ↔ _
    rw [comp_hom_eq_one_iff x (j ≫ ρ) σ.hom, Grp.comp_hom_hom, ← Category.assoc, hker]
    change _ ↔ x ≫ j.hom.hom ∈ (center G).carrier T
    rw [← mem_conjugationKernel_iff_centralizesJet]
    change (conjugationAction G n).kernel = center G at hn
    rw [hn]
  exact ⟨hq.1, hq.2.1, hq.2.2.1, hfull⟩

end Langlands.GroupScheme.Lie
