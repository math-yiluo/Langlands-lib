import Langlands.GroupScheme.Unipotent.HopfFixed
import Langlands.GroupScheme.Chevalley.SubspaceMatrix
import Langlands.GroupScheme.CorepresentedAffineComparison
import Langlands.GroupScheme.Reductive.Basic

/-! # Unipotent corepresented group schemes have unipotent coordinate bialgebras -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry TensorProduct Coalgebra Module
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Unipotent

open AffineLinearEmbedding Chevalley

variable {k : Type u} [Field k] {F : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} (CommRingCat.of k)} (e : (F ⋙ forget GrpCat).CorepresentableBy B)

/-- On an affine test scheme, the coordinates of a point of a corepresented group scheme are
its classifying algebra map followed by the inverse section comparison. -/
theorem homEquiv_symm_pointsEquiv_affine (S : CommAlgCat.{u} (CommRingCat.of k))
    (x : (algSpec (CommRingCat.of k)).obj (op S) ⟶ (Corepresented.groupScheme F e).X) :
    e.homEquiv.symm (Corepresented.pointsEquiv F e ((algSpec (CommRingCat.of k)).obj (op S)) x) =
      (algSpec.fullyFaithful.preimage (X := op S) (Y := op B) x).unop ≫
        (Corepresented.affineSectionsIso S).inv := by
  rw [Corepresented.pointsEquiv_eq_affinePointsEquiv, Corepresented.affinePointsEquiv_apply]
  change e.homEquiv.symm ((F ⋙ forget GrpCat).map (Corepresented.affineSectionsIso S).inv
    (e.homEquiv _)) = _
  rw [← e.homEquiv_comp, Equiv.symm_apply_apply]

/-- If a corepresented group scheme over a field is unipotent, its coordinate bialgebra has the
property that every nonzero finite-dimensional right-translation stable subspace contains `1`. -/
theorem oneMemStable_of_isUnipotent (hU : IsUnipotent (Corepresented.groupScheme F e)) :
    letI := bialgebra e
    OneMemStable k B := by
  let := bialgebra e
  intro V hfin hV hV0
  let N := finrank k V
  let b : Basis (Fin N) k V := Module.finBasis k V
  have : Nonempty (Fin N) :=
    ⟨⟨0, Nat.pos_of_ne_zero fun h => hV0 (Submodule.finrank_eq_zero.1 h)⟩⟩
  let hR : IsField (CommRingCat.of k) := Field.toIsField k
  let ρ := regularRepresentation e hR V b hV
  obtain ⟨v, hv0, hv⟩ := hU (Fin N) ρ
  let T := (algSpec (CommRingCat.of k)).obj (op B)
  let φ := (Corepresented.affineSectionsIso B).inv.hom
  have hφ : Function.Injective φ := by
    intro a a' h
    have h1 := ConcreteCategory.congr_hom (Corepresented.affineSectionsIso B).inv_hom_id a
    have h2 := ConcreteCategory.congr_hom (Corepresented.affineSectionsIso B).inv_hom_id a'
    exact h1.symm.trans ((congrArg (Corepresented.affineSectionsIso B).hom.hom h).trans h2)
  let x₀ : T ⟶ (Corepresented.groupScheme F e).X := 𝟙 _
  have hM : ∀ i j, (ρ.pointMatrix T x₀ : Matrix (Fin N) (Fin N) Γ(T.left, ⊤)) i j =
      φ (subspaceMatrix V b i j) := by
    intro i j
    refine (regularRepresentation_pointMatrix e hR V b hV T x₀ i j).trans ?_
    rw [homEquiv_symm_pointsEquiv_affine]
    have h0 : algSpec.fullyFaithful.preimage (X := op B) (Y := op B) x₀ = 𝟙 _ :=
      algSpec.fullyFaithful.preimage_id
    rw [h0, unop_id, Category.id_comp]
    rfl
  have hs : ∀ c : k, scalarMap T c = φ (algebraMap k B c) := by
    intro c
    rw [φ.commutes]
    rfl
  have hrow : ∀ i, ∑ j, v j • subspaceMatrix V b i j = v i • (1 : (B : Type u)) := by
    intro i
    apply hφ
    have h := congrFun (hv T x₀) i
    simp only [Matrix.mulVec, dotProduct, hM, hs] at h
    calc φ (∑ j, v j • subspaceMatrix V b i j)
        = ∑ j, φ (subspaceMatrix V b i j) * φ (algebraMap k B (v j)) := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Algebra.smul_def, map_mul, mul_comm]
      _ = φ (algebraMap k B (v i)) := h
      _ = φ (v i • (1 : (B : Type u))) := by rw [Algebra.smul_def, mul_one]
  -- The vector `y = ∑ v_j b_j` is right-translation invariant.
  let y : (B : Type u) := ∑ j, v j • (b j : (B : Type u))
  have hyV : y ∈ V := V.sum_mem fun j _ => V.smul_mem _ (b j).2
  have hy : comul (R := k) y = y ⊗ₜ[k] (1 : (B : Type u)) := by
    calc comul (R := k) y
        = ∑ j, ∑ i, (b i : (B : Type u)) ⊗ₜ[k] (v j • subspaceMatrix V b i j) := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [map_smul, comul_basis V b hV, Finset.smul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [TensorProduct.tmul_smul]
      _ = ∑ i, ∑ j, (b i : (B : Type u)) ⊗ₜ[k] (v j • subspaceMatrix V b i j) :=
          Finset.sum_comm
      _ = ∑ i, (v i • (b i : (B : Type u))) ⊗ₜ[k] (1 : (B : Type u)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← TensorProduct.tmul_sum, hrow, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
      _ = y ⊗ₜ[k] (1 : (B : Type u)) := by rw [← TensorProduct.sum_tmul]
  have hinv : ∀ g : Module.Dual k B, rightAct g y = g 1 • y := by
    intro g
    rw [rightAct_apply, hy, LinearMap.lTensor_tmul, TensorProduct.rid_tmul]
  obtain ⟨c, hc⟩ : ∃ c : k, y = c • (1 : (B : Type u)) :=
    ⟨_, eq_counit_smul_one_of_invariant hinv⟩
  have hy0 : y ≠ 0 := by
    intro h0
    apply hv0
    have hli : LinearIndependent k fun j => (b j : (B : Type u)) :=
      b.linearIndependent.map' V.subtype (Submodule.ker_subtype V)
    funext j
    exact Fintype.linearIndependent_iff.1 hli v h0 j
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    exact hy0 hc
  have h1 : (1 : (B : Type u)) = c⁻¹ • y := by
    rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  rw [h1]
  exact V.smul_mem _ hyV

/-- The point of a corepresented group scheme classified by an algebra map out of its
representing algebra. -/
abbrev classifiedPoint {S : CommAlgCat.{u} (CommRingCat.of k)} (f : B ⟶ S) :
    (algSpec (CommRingCat.of k)).obj (op S) ⟶ (Corepresented.groupScheme F e).X :=
  (algSpec (CommRingCat.of k)).map f.op

/-- The matrix of a representation of a corepresented group scheme at the universal point. -/
abbrev universalMatrix {n : Type} [Fintype n] [DecidableEq n]
    (ρ : MatrixRepresentation (Corepresented.groupScheme F e) n) : Matrix n n (B : Type u) :=
  (ρ.affineMatrix B (𝟙 ((algSpec (CommRingCat.of k)).obj (op B))) : Matrix n n (B : Type u))

variable {n : Type} [Fintype n] [DecidableEq n]
  (ρ : MatrixRepresentation (Corepresented.groupScheme F e) n)

/-- The matrix at the point classified by an algebra map is the universal matrix with that map
applied to its entries. -/
theorem affineMatrix_classifiedPoint (S : CommAlgCat.{u} (CommRingCat.of k)) (f : B ⟶ S) :
    (ρ.affineMatrix S (classifiedPoint e f) : Matrix n n S) = (universalMatrix e ρ).map f.hom :=
  congrArg Units.val ((congrArg (ρ.affineMatrix S)
    (Category.comp_id ((algSpec (CommRingCat.of k)).map f.op)).symm).trans
      (ρ.affineMatrix_naturality f (𝟙 ((algSpec (CommRingCat.of k)).obj (op B)))))

/-- The entries of the universal matrix are matrix coefficients: their comultiplication is
matrix multiplication. -/
theorem comul_universalMatrix (i j : n) :
    AffineLinearEmbedding.comul e (universalMatrix e ρ i j) =
      ∑ l, universalMatrix e ρ i l ⊗ₜ[k] universalMatrix e ρ l j := by
  let S := CommAlgCat.of (CommRingCat.of k) ((B : Type u) ⊗[k] (B : Type u))
  let fc : B ⟶ S := CommAlgCat.ofHom (AffineLinearEmbedding.comul e)
  let fl : B ⟶ S := CommAlgCat.ofHom Algebra.TensorProduct.includeLeft
  let fr : B ⟶ S := CommAlgCat.ofHom Algebra.TensorProduct.includeRight
  have hx : classifiedPoint e fc = classifiedPoint e fl * classifiedPoint e fr := by
    apply (Corepresented.affinePointsEquiv F e S).injective
    rw [map_mul, Corepresented.affinePointsEquiv_map, Corepresented.affinePointsEquiv_map,
      Corepresented.affinePointsEquiv_map]
    exact pt_comul e
  have h : (ρ.affineMatrix S (classifiedPoint e fc) : Matrix n n S) =
      (ρ.affineMatrix S (classifiedPoint e fl) : Matrix n n S) *
        (ρ.affineMatrix S (classifiedPoint e fr) : Matrix n n S) := by
    rw [hx, map_mul, Units.val_mul]
  rw [affineMatrix_classifiedPoint e ρ S fc, affineMatrix_classifiedPoint e ρ S fl,
    affineMatrix_classifiedPoint e ρ S fr] at h
  have h' := congrFun (congrFun h i) j
  rw [Matrix.map_apply, Matrix.mul_apply] at h'
  refine h'.trans (Finset.sum_congr rfl fun l _ => ?_)
  change (universalMatrix e ρ i l ⊗ₜ[k] (1 : (B : Type u))) *
    ((1 : (B : Type u)) ⊗ₜ[k] universalMatrix e ρ l j) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- The counit evaluates the universal matrix to the identity matrix. -/
theorem counit_universalMatrix (i j : n) :
    AffineLinearEmbedding.counit e (universalMatrix e ρ i j) = (1 : Matrix n n k) i j := by
  let S := CommAlgCat.of (CommRingCat.of k) k
  let fe : B ⟶ S := CommAlgCat.ofHom (AffineLinearEmbedding.counit e)
  have hx : classifiedPoint e fe = 1 := by
    apply (Corepresented.affinePointsEquiv F e S).injective
    rw [map_one, Corepresented.affinePointsEquiv_map]
    exact pt_homEquiv_symm e 1
  have h : (ρ.affineMatrix S (classifiedPoint e fe) : Matrix n n S) = 1 := by
    rw [hx, map_one, Units.val_one]
  rw [affineMatrix_classifiedPoint e ρ S fe] at h
  have h' := congrFun (congrFun h i) j
  rw [Matrix.map_apply] at h'
  exact h'

/-- Conversely, a corepresented group scheme over a field whose coordinate bialgebra has the
property that every nonzero finite-dimensional right-translation stable subspace contains `1` is
unipotent. -/
theorem isUnipotent_of_oneMemStable (hB : letI := bialgebra e; OneMemStable k B) :
    IsUnipotent (Corepresented.groupScheme F e) := by
  let := bialgebra e
  intro n _ _ _ ρ
  let N := universalMatrix e ρ
  have hcomul : ∀ i j, comul (R := k) (N i j) = ∑ l, N i l ⊗ₜ[k] N l j :=
    comul_universalMatrix e ρ
  have hcounit : ∀ i j, counit (R := k) (N i j) = (1 : Matrix n n k) i j :=
    counit_universalMatrix e ρ
  have hright : ∀ (g : Module.Dual k B) i l, rightAct g (N i l) = ∑ j, g (N j l) • N i j := by
    intro g i l
    rw [rightAct_apply, hcomul, map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LinearMap.lTensor_tmul, TensorProduct.rid_tmul]
  let T : Module.Dual k B → (n → k) →ₗ[k] (n → k) := fun g => (N.map g).mulVecLin
  let π : n → (n → k) →ₗ[k] (B : Type u) := fun i => Fintype.linearCombination k (N i)
  have hπ : ∀ i g v, π i (T g v) = rightAct g (π i v) := by
    intro i g v
    simp only [π, T, Fintype.linearCombination_apply, Matrix.mulVecLin_apply, Matrix.mulVec,
      dotProduct, Matrix.map_apply, map_sum, map_smul, hright, Finset.smul_sum, smul_smul,
      Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    rw [mul_comm]
  have hsep : ∀ v, (∀ i, π i v = 0) → v = 0 := by
    intro v hv
    funext i
    have h := congrArg (counit (R := k)) (hv i)
    simp only [π, Fintype.linearCombination_apply, map_sum, map_smul, hcounit, map_zero,
      Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, ↓reduceIte] at h
    exact h
  have htop : (⊤ : Submodule k (n → k)) ≠ ⊥ := by
    obtain ⟨i⟩ := ‹Nonempty n›
    intro h
    have h1 : (Pi.single i 1 : n → k) ∈ (⊥ : Submodule k (n → k)) := h ▸ Submodule.mem_top
    rw [Submodule.mem_bot] at h1
    simpa using congrFun h1 i
  obtain ⟨w, -, hw0, hw⟩ := exists_invariant hB T π hπ hsep ⊤ (fun _ _ _ => Submodule.mem_top)
    htop
  have hrow : ∀ i, ∑ j, w j • N i j = w i • (1 : (B : Type u)) := by
    intro i
    apply eq_of_forall_dual k
    intro g
    have h := congrFun (hw g) i
    simp only [T, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.map_apply,
      Pi.smul_apply, smul_eq_mul] at h
    rw [map_sum, map_smul, smul_eq_mul]
    simp only [map_smul, smul_eq_mul]
    rw [mul_comm (w i), ← h]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  refine ⟨w, hw0, fun T' g => ?_⟩
  let φ := (Corepresented.affineSectionsIso B).inv.hom
  let ψ : (B : Type u) →+* Γ(T'.left, ⊤) := g.left.appTop.hom.comp φ.toRingHom
  have hM : (ρ.pointMatrix T' g : Matrix n n Γ(T'.left, ⊤)) = N.map ψ :=
    congrArg Units.val (((congrArg (ρ.pointMatrix T') (Category.comp_id g).symm).trans
      (ρ.pointMatrix_naturality g (𝟙 ((algSpec (CommRingCat.of k)).obj (op B))))).trans
        (congrArg (Matrix.GeneralLinearGroup.map g.left.appTop.hom)
          (ρ.pointMatrix_eq_affineMatrix B (𝟙 ((algSpec (CommRingCat.of k)).obj (op B))))))
  have hs : ∀ c : k, scalarMap T' c = ψ (algebraMap k B c) := by
    intro c
    have hw' := Over.w g
    change _ = g.left.appTop.hom (φ (algebraMap k B c))
    rw [φ.commutes]
    simp only [scalarMap, ← hw', Scheme.Hom.comp_appTop]
    rfl
  funext i
  rw [hM]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, hs, ← map_mul, ← map_sum]
  congr 1
  rw [Algebra.algebraMap_eq_smul_one (w i), ← hrow i]
  exact Finset.sum_congr rfl fun j _ => by rw [Algebra.smul_def, mul_comm]

end Langlands.GroupScheme.Unipotent
