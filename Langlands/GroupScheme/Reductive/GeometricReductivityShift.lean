import Langlands.GroupScheme.Reductive.GeometricReductivityStatement
import Langlands.GroupScheme.Reductive.AdditiveShiftComodule
import Langlands.GroupScheme.Reductive.HomogeneousShiftConstant
import Langlands.GroupScheme.MatrixRepresentationDual
import Langlands.GroupScheme.VectorGroupQuotient

/-! # Geometric reductivity excludes coordinates shifted by a nonconstant function -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry TensorProduct Coalgebra
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The conclusion of geometric reductivity for one group scheme over a field: every nonzero fixed
vector of a coordinate representation is detected by an invariant homogeneous polynomial of
positive degree. -/
def IsGeometricallyReductive {k : Type u} [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) : Prop :=
  ∀ (n : Type) [Fintype n] [DecidableEq n] (ρ : MatrixRepresentation G n) (v : n → k),
    v ≠ 0 → ρ.IsFixedVector v →
    ∃ (d : ℕ) (F : MvPolynomial n k), 0 < d ∧ F.IsHomogeneous d ∧
      (∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X) (x : n → Γ(T.left, ⊤)),
        MvPolynomial.eval₂ (scalarMap T)
            ((ρ.pointMatrix T g : Matrix n n Γ(T.left, ⊤)) *ᵥ x) F =
          MvPolynomial.eval₂ (scalarMap T) x F) ∧
      MvPolynomial.eval v F ≠ 0

/-- Haboush's theorem gives the conclusion for every pseudo-reductive group over an algebraically
closed field. -/
theorem isGeometricallyReductive_of_statement (h : ReductiveGeometricReductivityStatement.{u})
    {k : Type u} [Field k] [IsAlgClosed k] {G : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsPseudoReductive G) : IsGeometricallyReductive G :=
  fun n _ _ ρ v hv hfix => h k G hG n ρ v hv hfix

/-- The conclusion of geometric reductivity transfers along isomorphisms. -/
theorem IsGeometricallyReductive.of_iso {k : Type u} [Field k]
    {G G' : GroupScheme (Spec (CommRingCat.of k))} (i : G' ≅ G)
    (h : IsGeometricallyReductive G) : IsGeometricallyReductive G' := by
  intro n _ _ ρ v hv hfix
  have hcomp : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G'.X),
      (g ≫ i.hom.hom.hom) ≫ i.inv.hom.hom = g := by
    intro T g
    rw [Category.assoc, ← Grp.comp_hom_hom, i.hom_inv_id, Grp.id_hom_hom, Category.comp_id]
  have hfix' : (ρ.restrict i.inv).IsFixedVector v := by
    intro T g
    rw [MatrixRepresentation.pointMatrix_restrict]
    exact hfix T _
  obtain ⟨d, F, hd, hF, hinv, hv'⟩ := h n (ρ.restrict i.inv) v hv hfix'
  refine ⟨d, F, hd, hF, fun T g x => ?_, hv'⟩
  have := hinv T (g ≫ i.hom.hom.hom) x
  rwa [MatrixRepresentation.pointMatrix_restrict, hcomp] at this

namespace AdditiveShift

open AffineLinearEmbedding Chevalley

variable {K : Type u} [Field K] {F : CommAlgCat.{u} (CommRingCat.of K) ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} (CommRingCat.of K)} (e : (F ⋙ forget GrpCat).CorepresentableBy B)

/-- Evaluation of coordinates at a point of the corepresented group over a test scheme. -/
abbrev evalAt {T : Over (Spec (CommRingCat.of K))}
    (x : T ⟶ (Corepresented.groupScheme F e).X) :
    B →ₐ[CommRingCat.of K] ((algΓ (CommRingCat.of K)).obj T).unop :=
  (e.homEquiv.symm (Corepresented.pointsEquiv F e T x)).hom

theorem evalAt_apply {T : Over (Spec (CommRingCat.of K))}
    (x : T ⟶ (Corepresented.groupScheme F e).X) (b : B) :
    evalAt e x b = x.left.appTop ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b) := by
  rw [evalAt, Corepresented.pointsEquiv_apply, Equiv.symm_apply_apply]
  exact Corepresented.adjunction_homEquiv_symm_apply x b

theorem algebraMap_algΓ (T : Over (Spec (CommRingCat.of K))) (c : K) :
    algebraMap (CommRingCat.of K) ((algΓ (CommRingCat.of K)).obj T).unop c = scalarMap T c :=
  rfl

/-- Over an algebraically closed field, a geometrically reductive corepresented group has no
coordinate `h` that is shifted by `ψ` under left translation along `φ`, unless `ψ` is a
scalar. -/
theorem false_of_isShift [IsAlgClosed K]
    (hG : IsGeometricallyReductive (Corepresented.groupScheme F e))
    {C : Type*} [CommRing C] [IsDomain C] [Algebra K C] (φ : B →ₐ[K] C) (ψ : C)
    (hψ : ψ ∉ Set.range (algebraMap K C)) (h : B)
    (hh : letI := bialgebra e; IsShift φ ψ h 1) : False := by
  let := bialgebra e
  have hR : IsField (CommRingCat.of K) := Field.toIsField K
  have hψ0 : ψ ≠ 0 := fun h0 => hψ ⟨0, by rw [h0, map_zero]⟩
  obtain ⟨lam, hlam⟩ := Module.Projective.exists_dual_eq_one K hψ0
  have hone : comul (R := K) (1 : B) = (1 : B) ⊗ₜ[K] (1 : B) := Bialgebra.comul_one
  have hε1 : counit (R := K) (1 : B) = 1 := Bialgebra.counit_one
  let V : Submodule K B := regularSpan (K := K) {h}
  have hV : ∀ (f : Module.Dual K B) (v : B), v ∈ V → rightAct f v ∈ V :=
    fun f _ hv => rightAct_mem_regularSpan {h} f hv
  have hVs : V ≤ shiftSubmodule φ ψ := regularSpan_le_shiftSubmodule hh hone
  have hhV : h ∈ V := subset_regularSpan {h} (Finset.mem_coe.mpr (Finset.mem_singleton_self h))
  let b := Module.finBasis K V
  let ρ0 := regularRepresentation e hR V b hV
  let ρ := ρ0.dual
  let ℓ : Fin (Module.finrank K V) → K := fun i => shiftCoeff φ lam (b i : B)
  have hshift : ∀ i, IsShift φ ψ (b i : B) (ℓ i) := by
    intro i
    obtain ⟨a, ha⟩ := hVs (b i).2
    have hae := ha.eq_shiftCoeff hε1 hlam
    subst hae
    exact ha
  -- the shift coefficients do not all vanish, since `h` has shift coefficient `1`
  have hℓ0 : ℓ ≠ 0 := by
    intro h0
    have h1 : shiftCoeff φ lam h = 1 := (hh.eq_shiftCoeff hε1 hlam).symm
    rw [← basis_expand V b hhV, map_sum] at h1
    simp only [map_smul] at h1
    have : ∀ i, shiftCoeff φ lam (b i : B) = 0 := fun i => congrFun h0 i
    simp [this] at h1
  -- the shift coefficients are fixed by the dual representation
  have hfixT : ∀ (T : Over (Spec (CommRingCat.of K)))
      (g : T ⟶ (Corepresented.groupScheme F e).X),
      ((ρ0.pointMatrix T g : Matrix _ _ Γ(T.left, ⊤))ᵀ *ᵥ fun i => scalarMap T (ℓ i)) =
        fun i => scalarMap T (ℓ i) := by
    intro T g
    funext j
    have hA : ∀ i, (ρ0.pointMatrix T g : Matrix _ _ Γ(T.left, ⊤)) i j =
        evalAt e g (subspaceMatrix V b i j) := fun i =>
      regularRepresentation_pointMatrix e hR V b hV T g i j
    have key := congrArg (evalAt e g) (sum_shiftCoeff_smul_subspaceMatrix V b hV hVs hε1 hlam j)
    rw [map_sum] at key
    simp only [Algebra.smul_def, map_mul, mul_one] at key
    have hc : ∀ c : K, evalAt e g (algebraMap K B c) = scalarMap T c := fun c =>
      (evalAt e g).commutes c
    simp only [hc] at key
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, hA]
    exact (Finset.sum_congr rfl fun i _ => mul_comm _ _).trans key
  have hfix : ρ.IsFixedVector ℓ := by
    intro T g
    rw [MatrixRepresentation.dual_pointMatrix, GeneralLinear.matrixContragredient_coe]
    set A := ρ0.pointMatrix T g
    conv_lhs => rw [← hfixT T g]
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul]
    change ((A * A⁻¹ : Matrix.GeneralLinearGroup _ _).val)ᵀ *ᵥ _ = _
    rw [mul_inv_cancel]
    simp
  obtain ⟨d, P, hd, hP, hinv, hPℓ⟩ := hG _ ρ ℓ hℓ0 hfix
  -- evaluate the invariance at the inverse of the universal point
  let T : Over (Spec (CommRingCat.of K)) := (Corepresented.groupScheme F e).X
  let u : T ⟶ (Corepresented.groupScheme F e).X := 𝟙 _
  let ε₁ : Fin (Module.finrank K V) → K := fun i => counit (R := K) (b i : B)
  have hinv' := hinv T u⁻¹ fun i => scalarMap T (ε₁ i)
  have hmat : (ρ.pointMatrix T u⁻¹ : Matrix (Fin (Module.finrank K V))
      (Fin (Module.finrank K V)) Γ(T.left, ⊤)) =
      (ρ0.pointMatrix T u : Matrix (Fin (Module.finrank K V))
        (Fin (Module.finrank K V)) Γ(T.left, ⊤))ᵀ := by
    rw [MatrixRepresentation.dual_pointMatrix, GeneralLinear.matrixContragredient_coe, map_inv,
      inv_inv]
  have hvec : ((ρ.pointMatrix T u⁻¹ : Matrix _ _ Γ(T.left, ⊤)) *ᵥ
      fun i => scalarMap T (ε₁ i)) = fun j => evalAt e u (b j : B) := by
    rw [hmat]
    funext j
    have hA : ∀ i, (ρ0.pointMatrix T u : Matrix _ _ Γ(T.left, ⊤)) i j =
        evalAt e u (subspaceMatrix V b i j) := fun i =>
      regularRepresentation_pointMatrix e hR V b hV T u i j
    have key := congrArg (evalAt e u) (basis_eq_sum_counit V b hV j)
    rw [map_sum] at key
    simp only [Algebra.smul_def, map_mul] at key
    have hc : ∀ c : K, evalAt e u (algebraMap K B c) = scalarMap T c := fun c =>
      (evalAt e u).commutes c
    simp only [hc] at key
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, hA]
    exact (Finset.sum_congr rfl fun i _ => mul_comm _ _).trans key.symm
  rw [hvec] at hinv'
  -- the invariant polynomial is constant on the basis coordinates
  let c : K := MvPolynomial.eval ε₁ P
  have hinj : Function.Injective (evalAt e u) := by
    intro x y hxy
    rw [evalAt_apply, evalAt_apply] at hxy
    simp only [u, Over.id_left, Scheme.Hom.id_appTop] at hxy
    exact (Scheme.ΓSpecIso (CommRingCat.of B)).commRingCatIsoToRingEquiv.symm.injective hxy
  have hB : MvPolynomial.aeval (fun j => (b j : B)) P = algebraMap K B c := by
    apply hinj
    have h1 : evalAt e u (MvPolynomial.aeval (fun j => (b j : B)) P) =
        MvPolynomial.eval₂ (scalarMap T) (fun j => evalAt e u (b j : B)) P := by
      rw [MvPolynomial.comp_aeval_apply]
      rfl
    have h2 : evalAt e u (algebraMap K B c) =
        MvPolynomial.eval₂ (scalarMap T) (fun i => scalarMap T (ε₁ i)) P := by
      rw [(evalAt e u).commutes c]
      change scalarMap T (MvPolynomial.eval₂ (RingHom.id K) ε₁ P) = _
      rw [MvPolynomial.eval₂_comp_left, RingHom.comp_id]
      rfl
    rw [h1, h2, hinv']
  -- restrict to the subgroup along `φ`
  have hC : MvPolynomial.aeval (fun j => algebraMap K C (ε₁ j) + algebraMap K C (ℓ j) * ψ) P =
      algebraMap K C c := by
    have h1 := congrArg φ hB
    rw [AlgHom.commutes] at h1
    rw [← h1, MvPolynomial.comp_aeval_apply]
    refine congrArg (fun f => MvPolynomial.aeval f P) (funext fun j => ?_)
    rw [(hshift j).map_eq hε1, Algebra.smul_def]
  exact hψ (HomogeneousShift.mem_range_of_aeval_shift hd hP ε₁ ℓ hPℓ ψ c hC)

end AdditiveShift

end Langlands.GroupScheme
