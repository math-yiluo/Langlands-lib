import Langlands.GroupScheme.Trigonalizable.MatrixCriterion
import Langlands.GroupScheme.Trigonalizable
import Langlands.GroupScheme.Unipotent.CoordinateBialgebra
import Langlands.GroupScheme.Unipotent.ScalarExtension
import Langlands.GroupScheme.MatrixRepresentation

/-! # Trigonalizable group schemes and semi-invariant lines in coordinate bialgebras

A group scheme corepresented by a bialgebra `B` over a field is trigonalizable exactly when
every nonzero finite-dimensional right-translation stable subspace of `B` contains a nonzero
semi-invariant `y`, that is, `comul y = y ⊗ χ` for some `χ`. This coordinate property survives
extension of scalars along a field extension.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry TensorProduct Coalgebra Module

namespace Langlands.GroupScheme.Trigonalizable

open AffineLinearEmbedding Chevalley Unipotent

/-- Every nonzero finite-dimensional right-translation stable subspace of the bialgebra contains a
nonzero semi-invariant: an element `y` with `comul y = y ⊗ χ` for some `χ`. -/
abbrev LineStable (K B : Type*) [Field K] [Ring B] [Bialgebra K B] : Prop :=
  ∀ V : Submodule K B, FiniteDimensional K V →
    (∀ (f : Module.Dual K B) (v : B), v ∈ V → rightAct f v ∈ V) → V ≠ ⊥ →
      ∃ y ∈ V, y ≠ 0 ∧ ∃ χ : B, comul (R := K) y = y ⊗ₜ[K] χ

section Bialgebra

variable {K : Type*} [Field K] {B : Type*} [Ring B] [Bialgebra K B]

/-- Right translation multiplies a semi-invariant by the value of the functional at its
multiplier. -/
theorem rightAct_of_comul_eq {y χ : B} (h : comul (R := K) y = y ⊗ₜ[K] χ)
    (g : Module.Dual K B) : rightAct g y = g χ • y := by
  rw [rightAct_apply, h, LinearMap.lTensor_tmul, TensorProduct.rid_tmul]

/-- A nonzero finite-dimensional stable subspace of a module with a jointly injective family of
intertwining maps to a bialgebra with the property `LineStable` contains a nonzero vector on
which every translation acts by a scalar given by one multiplier `χ`. -/
theorem exists_semiInvariant (hB : LineStable K B)
    {M : Type*} [AddCommGroup M] [Module K M] (T : Module.Dual K B → M →ₗ[K] M)
    {I : Type*} (π : I → M →ₗ[K] B)
    (hπ : ∀ i g m, π i (T g m) = rightAct g (π i m))
    (hsep : ∀ m, (∀ i, π i m = 0) → m = 0)
    (W : Submodule K M) [FiniteDimensional K W]
    (hW : ∀ g m, m ∈ W → T g m ∈ W) (hW0 : W ≠ ⊥) :
    ∃ w ∈ W, w ≠ 0 ∧ ∃ χ : B, ∀ g, T g w = g χ • w := by
  induction hd : finrank K W using Nat.strong_induction_on generalizing W with
  | _ d ih =>
    obtain ⟨w₀, hw₀, hw₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
    obtain ⟨i, hi⟩ : ∃ i, π i w₀ ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hw₀0 (hsep w₀ hc)
    by_cases hW' : W ⊓ LinearMap.ker (π i) = ⊥
    · obtain ⟨y, ⟨w, hw, rfl⟩, hy0, χ, hχ⟩ := hB (W.map (π i)) inferInstance
        (by
          rintro f _ ⟨m, hm, rfl⟩
          exact ⟨T f m, hW f m hm, hπ i f m⟩)
        (by
          intro h
          apply hi
          have : π i w₀ ∈ W.map (π i) := ⟨w₀, hw₀, rfl⟩
          rw [h] at this
          exact (Submodule.mem_bot K).1 this)
      refine ⟨w, hw, ?_, χ, fun g => ?_⟩
      · rintro rfl
        exact hy0 (map_zero _)
      · have hmem : T g w - g χ • w ∈ W ⊓ LinearMap.ker (π i) := by
          refine Submodule.mem_inf.2 ⟨W.sub_mem (hW g w hw) (W.smul_mem _ hw), ?_⟩
          rw [LinearMap.mem_ker, map_sub, map_smul, hπ, rightAct_of_comul_eq hχ, sub_self]
        rw [hW'] at hmem
        exact sub_eq_zero.mp ((Submodule.mem_bot K).1 hmem)
    · have hle : W ⊓ LinearMap.ker (π i) ≤ W := inf_le_left
      have : FiniteDimensional K ↥(W ⊓ LinearMap.ker (π i)) :=
        Submodule.finiteDimensional_of_le hle
      have hlt : W ⊓ LinearMap.ker (π i) < W := by
        refine lt_of_le_of_ne hle fun h => hi ?_
        have : w₀ ∈ W ⊓ LinearMap.ker (π i) := by rw [h]; exact hw₀
        exact (Submodule.mem_inf.1 this).2
      obtain ⟨w, hw, hw0, hinv⟩ := ih _
        (by rw [← hd]; exact Submodule.finrank_lt_finrank_of_lt hlt) _
        (fun g m hm => Submodule.mem_inf.2 ⟨hW g m (Submodule.mem_inf.1 hm).1, by
          rw [LinearMap.mem_ker, hπ, LinearMap.mem_ker.1 (Submodule.mem_inf.1 hm).2, map_zero]⟩)
        hW' rfl
      exact ⟨w, (Submodule.mem_inf.1 hw).1, hw0, hinv⟩

end Bialgebra

section Corepresented

variable {k : Type u} [Field k] {F : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} (CommRingCat.of k)} (e : (F ⋙ forget GrpCat).CorepresentableBy B)

/-- If a corepresented group scheme over a field is trigonalizable, every nonzero
finite-dimensional right-translation stable subspace of its coordinate bialgebra contains a
nonzero semi-invariant. -/
theorem lineStable_of_isTrigonalizable (hT : IsTrigonalizable (Corepresented.groupScheme F e)) :
    letI := bialgebra e
    LineStable k B := by
  let := bialgebra e
  intro V hfin hV hV0
  let N := finrank k V
  let b : Basis (Fin N) k V := Module.finBasis k V
  have : Nonempty (Fin N) :=
    ⟨⟨0, Nat.pos_of_ne_zero fun h => hV0 (Submodule.finrank_eq_zero.1 h)⟩⟩
  let hR : IsField (CommRingCat.of k) := Field.toIsField k
  let ρ := regularRepresentation e hR V b hV
  obtain ⟨v, hv0, hv⟩ := hT (Fin N) ρ
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
  obtain ⟨c, hc⟩ := hv T x₀
  have hφs : Function.Surjective φ := fun c =>
    ⟨_, CommAlgCat.inv_hom_apply (Corepresented.affineSectionsIso B) c⟩
  obtain ⟨χ, rfl⟩ := hφs c
  have hrow : ∀ i, ∑ j, v j • subspaceMatrix V b i j = v i • χ := by
    intro i
    apply hφ
    have h := congrFun hc i
    simp only [Matrix.mulVec, dotProduct, hM, hs] at h
    calc φ (∑ j, v j • subspaceMatrix V b i j)
        = ∑ j, φ (subspaceMatrix V b i j) * φ (algebraMap k B (v j)) := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Algebra.smul_def, map_mul, mul_comm]
      _ = φ χ * φ (algebraMap k B (v i)) := h
      _ = φ (v i • χ) := by rw [Algebra.smul_def, map_mul, mul_comm]
  -- The vector `y = ∑ v_j b_j` is a semi-invariant with multiplier `χ`.
  let y : (B : Type u) := ∑ j, v j • (b j : (B : Type u))
  have hyV : y ∈ V := V.sum_mem fun j _ => V.smul_mem _ (b j).2
  have hy : comul (R := k) y = y ⊗ₜ[k] χ := by
    calc comul (R := k) y
        = ∑ j, ∑ i, (b i : (B : Type u)) ⊗ₜ[k] (v j • subspaceMatrix V b i j) := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [map_smul, comul_basis V b hV, Finset.smul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [TensorProduct.tmul_smul]
      _ = ∑ i, ∑ j, (b i : (B : Type u)) ⊗ₜ[k] (v j • subspaceMatrix V b i j) :=
          Finset.sum_comm
      _ = ∑ i, (v i • (b i : (B : Type u))) ⊗ₜ[k] χ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← TensorProduct.tmul_sum, hrow, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
      _ = y ⊗ₜ[k] χ := by rw [← TensorProduct.sum_tmul]
  have hy0 : y ≠ 0 := by
    intro h0
    apply hv0
    have hli : LinearIndependent k fun j => (b j : (B : Type u)) :=
      b.linearIndependent.map' V.subtype (Submodule.ker_subtype V)
    funext j
    exact Fintype.linearIndependent_iff.1 hli v h0 j
  exact ⟨y, hyV, hy0, χ, hy⟩

/-- Conversely, a corepresented group scheme over a field whose coordinate bialgebra has the
property `LineStable` is trigonalizable. -/
theorem isTrigonalizable_of_lineStable (hB : letI := bialgebra e; LineStable k B) :
    IsTrigonalizable (Corepresented.groupScheme F e) := by
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
  obtain ⟨w, -, hw0, χ, hw⟩ := exists_semiInvariant hB T π hπ hsep ⊤
    (fun _ _ _ => Submodule.mem_top) htop
  have hrow : ∀ i, ∑ j, w j • N i j = w i • χ := by
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
  refine ⟨ψ χ, ?_⟩
  funext i
  rw [hM]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, hs, Pi.smul_apply, smul_eq_mul,
    ← map_mul, ← map_sum]
  congr 1
  rw [mul_comm χ, ← Algebra.smul_def, ← hrow i]
  exact Finset.sum_congr rfl fun j _ => by rw [Algebra.smul_def, mul_comm]

end Corepresented

section ScalarExtension

/-- Tensors are separated by contracting the second factor with functionals. -/
theorem tensor_ext_right {k : Type*} [Field k] {M N : Type*} [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N] {t t' : M ⊗[k] N}
    (h : ∀ g : Module.Dual k N,
      TensorProduct.rid k M (g.lTensor M t) = TensorProduct.rid k M (g.lTensor M t')) :
    t = t' := by
  classical
  let b := Basis.ofVectorSpace k N
  have key : ∀ (u : M ⊗[k] N) (i : Basis.ofVectorSpaceIndex k N),
      TensorProduct.equivFinsuppOfBasisRight b u i =
        TensorProduct.rid k M ((b.coord i).lTensor M u) := by
    intro u i
    induction u using TensorProduct.inductionOn with
    | tmul x y => simp
    | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  apply (TensorProduct.equivFinsuppOfBasisRight b).injective
  ext i
  rw [key, key, h]

variable {k : Type*} [Field k] (K : Type*) [Field K] [Algebra k K] {B : Type*} [Ring B]
  [Bialgebra k B]

/-- An element of `K ⊗[k] B` on which every scalar-extended right translation acts by the value
of the functional at `χ` is a semi-invariant of the `K`-bialgebra `K ⊗[k] B` with multiplier
`1 ⊗ χ`. -/
theorem comul_baseChange_of_semiInvariant {w : K ⊗[k] B} {χ : B}
    (hw : ∀ g : Module.Dual k B, (rightAct g).lTensor K w = g χ • w) :
    comul (R := K) w = w ⊗ₜ[K] ((1 : K) ⊗ₜ[k] χ) := by
  let Φ : (K ⊗[k] B) ⊗[k] B →ₗ[k] (K ⊗[k] B) ⊗[K] (K ⊗[k] B) :=
    TensorProduct.lift
      (((TensorProduct.mk K (K ⊗[k] B) (K ⊗[k] B)).restrictScalars₁₂ k k).compl₂
        (Algebra.TensorProduct.includeRight (R := k) (A := K) (B := B)).toLinearMap)
  have hΦ : ∀ m b, Φ (m ⊗ₜ[k] b) = m ⊗ₜ[K] ((1 : K) ⊗ₜ[k] b) := fun _ _ => rfl
  have h1 : ∀ x : K ⊗[k] B, comul (R := K) x =
      Φ ((TensorProduct.assoc k K B B).symm ((comul (R := k) (A := B)).lTensor K x)) := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul c b =>
      rw [TensorProduct.comul_tmul, CommSemiring.comul_apply, LinearMap.lTensor_tmul]
      generalize comul (R := k) b = t
      induction t using TensorProduct.inductionOn with
      | tmul x y =>
        rw [AlgebraTensorModule.tensorTensorTensorComm_tmul, TensorProduct.assoc_symm_tmul, hΦ]
        have e1 : (c ⊗ₜ[k] y : K ⊗[k] B) = c • ((1 : K) ⊗ₜ[k] y) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        have e2 : (c ⊗ₜ[k] x : K ⊗[k] B) = c • ((1 : K) ⊗ₜ[k] x) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [e1, e2, TensorProduct.tmul_smul]
        exact TensorProduct.smul_tmul' _ _ _
      | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
    | add x y hx hy => simp only [map_add, hx, hy]
  have h2 : ∀ (g : Module.Dual k B) (x : K ⊗[k] B),
      TensorProduct.rid k (K ⊗[k] B) (g.lTensor (K ⊗[k] B)
        ((TensorProduct.assoc k K B B).symm ((comul (R := k) (A := B)).lTensor K x))) =
        (rightAct g).lTensor K x := by
    intro g x
    induction x using TensorProduct.inductionOn with
    | tmul c b =>
      rw [LinearMap.lTensor_tmul, LinearMap.lTensor_tmul, rightAct_apply]
      generalize comul (R := k) b = t
      induction t using TensorProduct.inductionOn with
      | tmul x y => simp [TensorProduct.tmul_smul]
      | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
    | add x y hx hy => simp only [map_add, hx, hy]
  have h3 : (TensorProduct.assoc k K B B).symm ((comul (R := k) (A := B)).lTensor K w) =
      w ⊗ₜ[k] χ := by
    apply tensor_ext_right
    intro g
    rw [h2, hw, LinearMap.lTensor_tmul, TensorProduct.rid_tmul]
  rw [h1, h3, hΦ]

/-- The property `LineStable` is preserved by extension of scalars of the bialgebra. -/
theorem LineStable.baseChange (hB : LineStable k B) : LineStable K (K ⊗[k] B) := by
  classical
  intro V hfin hV hV0
  -- The `k`-linear translation operators and the coordinate projections.
  let T : Module.Dual k B → (K ⊗[k] B) →ₗ[k] (K ⊗[k] B) := fun g => (rightAct g).lTensor K
  let π : Module.Dual k K → (K ⊗[k] B) →ₗ[k] B := fun l => TensorProduct.lid k B ∘ₗ l.rTensor B
  have hπ : ∀ l g m, π l (T g m) = rightAct g (π l m) := by
    intro l g m
    induction m using TensorProduct.inductionOn with
    | tmul c b => simp [π, T]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hsep : ∀ m, (∀ l, π l m = 0) → m = 0 := fun m hm => tensor_ext_left hm
  have hTV : ∀ g m, m ∈ V → T g m ∈ V := by
    intro g m hm
    change (rightAct g).lTensor K m ∈ V
    rw [← rightAct_baseChange]
    exact hV _ _ hm
  -- A nonzero vector of `V` and a finite-dimensional stable `k`-subspace containing it.
  obtain ⟨v₀, hv₀, hv₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV0
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset v₀
  let L : Submodule k K := Submodule.span k (S.image Prod.fst : Set K)
  let U : Submodule k B := regularSpan (K := k) (S.image Prod.snd)
  let j : L ⊗[k] U →ₗ[k] K ⊗[k] B := TensorProduct.map L.subtype U.subtype
  have hj : ∀ g, T g ∘ₗ j =
      j ∘ₗ ((rightAct g).restrict fun _ hb => rightAct_mem_regularSpan _ g hb).lTensor L := by
    intro g
    apply TensorProduct.ext'
    intro c b
    rfl
  let W : Submodule k (K ⊗[k] B) := LinearMap.range j ⊓ V.restrictScalars k
  have hW : ∀ g m, m ∈ W → T g m ∈ W := by
    rintro g m ⟨⟨y, rfl⟩, hm⟩
    exact ⟨⟨_, (LinearMap.congr_fun (hj g) y).symm⟩, hTV g _ hm⟩
  have hv₀W : v₀ ∈ W := by
    refine ⟨?_, hv₀⟩
    rw [hS]
    refine Submodule.sum_mem _ fun p hp => ?_
    have hc : p.1 ∈ L := Submodule.subset_span (Finset.mem_image_of_mem _ hp)
    have hb : p.2 ∈ U := subset_regularSpan _ (Finset.mem_image_of_mem _ hp)
    exact ⟨⟨p.1, hc⟩ ⊗ₜ ⟨p.2, hb⟩, rfl⟩
  have hW0 : W ≠ ⊥ := fun h => hv₀0 ((Submodule.mem_bot k).1 (h ▸ hv₀W))
  obtain ⟨w, hwW, hw0, χ, hw⟩ := exists_semiInvariant hB T π hπ hsep W hW hW0
  exact ⟨w, (Submodule.restrictScalars_mem k V w).1 hwW.2, hw0, (1 : K) ⊗ₜ[k] χ,
    comul_baseChange_of_semiInvariant K hw⟩

end ScalarExtension

end Langlands.GroupScheme.Trigonalizable
