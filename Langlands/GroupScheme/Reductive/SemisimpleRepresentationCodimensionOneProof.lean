import Langlands.GroupScheme.Reductive.SemisimpleRepresentationCodimensionOneStatement
import Langlands.GroupScheme.MatrixRepresentation.MinimalStableSubrepresentation
import Langlands.GroupScheme.MatrixRepresentation.QuotientCoordinates
import Langlands.GroupScheme.MatrixRepresentation.CoordinateLineCharacter
import Langlands.GroupScheme.MatrixRepresentation.NormalFixedCoordinates
import Langlands.GroupScheme.MatrixRepresentationTensor

/-! # Semisimplicity through complements of codimension one (proof) -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.SemisimpleRepresentationCodimensionOne

open MatrixRepresentation

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-! ### Stable subspaces -/

/-- The `k`-linear map `v ↦ (ℓ ((ρ(x) v)ᵢ))ᵢ` used in the definition of stability. -/
def coefficientMap (ρ : MatrixRepresentation G n) (A : CommAlgCat.{u} (CommRingCat.of k))
    (x : (algSpec (CommRingCat.of k)).obj (op A) ⟶ G.X) (ℓ : A →ₗ[k] k) :
    (n → k) →ₗ[k] (n → k) where
  toFun v := fun i => ℓ (((ρ.affineMatrix A x : Matrix n n A) *ᵥ
    (fun j => algebraMap k A (v j))) i)
  map_add' v w := by
    have h : (fun j => algebraMap k A (v j) + algebraMap k A (w j)) =
        (fun j => algebraMap k A (v j)) + (fun j => algebraMap k A (w j)) := rfl
    funext i
    simp only [Pi.add_apply, map_add]
    rw [h, Matrix.mulVec_add, Pi.add_apply, map_add]
  map_smul' c v := by
    have h : (fun j => algebraMap k A (c • v j)) =
        c • (fun j => algebraMap k A (v j)) := by
      funext j
      simp [Algebra.smul_def]
    funext i
    simp only [Pi.smul_apply, RingHom.id_apply]
    rw [h, Matrix.mulVec_smul, Pi.smul_apply, map_smul]

theorem isStableSubspace_iff_le_comap (ρ : MatrixRepresentation G n)
    (V : Submodule k (n → k)) :
    ρ.IsStableSubspace V ↔ ∀ A x ℓ, V ≤ V.comap (coefficientMap ρ A x ℓ) :=
  ⟨fun h A x ℓ _ hv => h A x _ hv ℓ, fun h A x _ hv ℓ => h A x ℓ hv⟩

/-- A supremum of stable subspaces is stable. -/
theorem isStableSubspace_sSup (ρ : MatrixRepresentation G n)
    (S : Set (Submodule k (n → k))) (hS : ∀ V ∈ S, ρ.IsStableSubspace V) :
    ρ.IsStableSubspace (sSup S) := by
  rw [isStableSubspace_iff_le_comap]
  intro A x ℓ
  apply sSup_le
  intro V hV
  exact ((isStableSubspace_iff_le_comap ρ V).mp (hS V hV) A x ℓ).trans
    (Submodule.comap_mono (le_sSup hV))

/-- An intersection of two stable subspaces is stable. -/
theorem isStableSubspace_inf {ρ : MatrixRepresentation G n} {V W : Submodule k (n → k)}
    (hV : ρ.IsStableSubspace V) (hW : ρ.IsStableSubspace W) :
    ρ.IsStableSubspace (V ⊓ W) :=
  fun A x v hv ℓ => ⟨hV A x v hv.1 ℓ, hW A x v hv.2 ℓ⟩

/-- Simple stable subspaces. -/
def IsSimpleStable (ρ : MatrixRepresentation G n) (W : Submodule k (n → k)) : Prop :=
  ρ.IsStableSubspace W ∧ W ≠ ⊥ ∧
    ∀ U : Submodule k (n → k), ρ.IsStableSubspace U → U ≤ W → U = ⊥ ∨ U = W

/-- Every nonzero stable subspace contains a simple stable subspace. -/
theorem exists_isSimpleStable_le (ρ : MatrixRepresentation G n)
    {W : Submodule k (n → k)} (hW : ρ.IsStableSubspace W) (hW0 : W ≠ ⊥) :
    ∃ S, IsSimpleStable ρ S ∧ S ≤ W := by
  classical
  let P : ℕ → Prop := fun d => ∃ S : Submodule k (n → k),
    ρ.IsStableSubspace S ∧ S ≠ ⊥ ∧ S ≤ W ∧ Module.finrank k S = d
  have hP : ∃ d, P d := ⟨_, W, hW, hW0, le_rfl, rfl⟩
  obtain ⟨S, hS, hS0, hSW, hdim⟩ := Nat.find_spec hP
  refine ⟨S, ⟨hS, hS0, ?_⟩, hSW⟩
  intro U hU hUS
  by_cases hU0 : U = ⊥
  · exact Or.inl hU0
  · right
    apply Submodule.eq_of_le_of_finrank_le hUS
    rw [hdim]
    exact Nat.find_min' hP ⟨U, hU, hU0, hUS.trans hSW, rfl⟩

/-- A stable subspace has coordinates: a representation on `kᵈ` and an injective
intertwiner onto it. -/
theorem exists_subCoordinates [IsAffineHom G.X.hom] (ρ : MatrixRepresentation G n)
    {V : Submodule k (n → k)} (hV : ρ.IsStableSubspace V) :
    ∃ (d : ℕ) (σ : MatrixRepresentation G (Fin d)) (B : Matrix n (Fin d) k),
      Intertwines σ ρ B ∧ Function.Injective B.mulVecLin ∧
        LinearMap.range B.mulVecLin = V ∧ Module.finrank k V = d := by
  obtain ⟨d, B, C, hCB, hcols, hproj⟩ := exists_subspace_split_coordinates V
  have hstable := hV.isStableCoordinates B C hcols hproj
  have hi : Function.Injective B.mulVecLin :=
    coordinateInclusion_injective (R := CommRingCat.of k) B C hCB
  have hr := range_coordinateInclusion_eq V B C hcols hproj
  refine ⟨d, restrictCoordinates ρ B C hCB hstable, B,
    intertwines_restrictCoordinates ρ B C hCB hstable, hi, hr, ?_⟩
  rw [← hr, LinearMap.finrank_range_of_inj hi, Module.finrank_fin_fun]

/-! ### (a) ⇒ (b) and complements ⇒ (a) -/

/-- If the simple stable subspaces span, every stable subspace of codimension one has a
stable complement. -/
theorem hasComplement_of_sSup_eq_top {N : ℕ} (ρ : MatrixRepresentation G (Fin N))
    (ha : sSup {W | IsSimpleStable ρ W} = ⊤) (W : Submodule k (Fin N → k))
    (hW : ρ.IsStableSubspace W) (hdim : Module.finrank k W + 1 = N) :
    ∃ W', ρ.IsStableSubspace W' ∧ IsCompl W W' := by
  have hWtop : W ≠ ⊤ := by
    intro h
    rw [h, finrank_top, Module.finrank_fin_fun] at hdim
    omega
  obtain ⟨S, hS, hSW⟩ : ∃ S, IsSimpleStable ρ S ∧ ¬ S ≤ W := by
    by_contra hcon
    push Not at hcon
    apply hWtop
    rw [eq_top_iff, ← ha]
    exact sSup_le hcon
  have hdisj : W ⊓ S = ⊥ := by
    rcases hS.2.2 (W ⊓ S) (isStableSubspace_inf hW hS.1) inf_le_right with h | h
    · exact h
    · exact absurd (h ▸ inf_le_left) hSW
  have hsup : W ⊔ S = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have hlt : W < W ⊔ S := lt_of_le_of_ne le_sup_left
      (fun h => hSW (h ▸ le_sup_right))
    have h1 := Submodule.finrank_lt_finrank_of_lt hlt
    have h2 := Submodule.finrank_le (W ⊔ S)
    rw [Module.finrank_fin_fun] at h2 ⊢
    omega
  exact ⟨S, hS.1, disjoint_iff.mpr hdisj, codisjoint_iff.mpr hsup⟩

/-- If every stable subspace has a stable complement, the simple stable subspaces span. -/
theorem sSup_eq_top_of_hasComplement (ρ : MatrixRepresentation G n)
    (h : ∀ W, ρ.IsStableSubspace W → ∃ W', ρ.IsStableSubspace W' ∧ IsCompl W W') :
    sSup {W | IsSimpleStable ρ W} = ⊤ := by
  have hT : ρ.IsStableSubspace (sSup {W | IsSimpleStable ρ W}) :=
    isStableSubspace_sSup ρ _ (fun V hV => hV.1)
  obtain ⟨C, hC, hTC⟩ := h _ hT
  by_contra hne
  have hC0 : C ≠ ⊥ := by
    intro hC0
    rw [hC0] at hTC
    exact hne (codisjoint_bot.mp hTC.codisjoint)
  obtain ⟨S, hS, hSC⟩ := exists_isSimpleStable_le ρ hC hC0
  apply hS.2.1
  rw [eq_bot_iff]
  exact (le_inf (le_sSup (show S ∈ {W | IsSimpleStable ρ W} from hS)) hSC).trans hTC.disjoint.le_bot

/-! ### (c) ⇒ (b) -/

omit [DecidableEq n] [Fintype m] [DecidableEq m] in
/-- Dimension count along a linear map whose kernel lies in the subspace. -/
theorem finrank_map_add_finrank_ker (Q : Matrix m n k) {X : Submodule k (n → k)}
    (hX : LinearMap.ker Q.mulVecLin ≤ X) :
    Module.finrank k (X.map Q.mulVecLin) + Module.finrank k (LinearMap.ker Q.mulVecLin) =
      Module.finrank k X := by
  have h := LinearMap.finrank_range_add_finrank_ker (Q.mulVecLin ∘ₗ X.subtype)
  rw [LinearMap.range_comp, Submodule.range_subtype, LinearMap.ker_comp] at h
  rw [← h, (Submodule.comapSubtypeEquivOfLe hX).finrank_eq]

/-- Transport of a simple stable subspace along an injective intertwiner onto a
subspace containing it. -/
theorem isSimpleStable_comap {ρ : MatrixRepresentation G n} {σ : MatrixRepresentation G m}
    {B : Matrix n m k} (hB : Intertwines σ ρ B) (hBi : Function.Injective B.mulVecLin)
    {U : Submodule k (n → k)} (hU : IsSimpleStable ρ U)
    (hUB : U ≤ LinearMap.range B.mulVecLin) :
    IsSimpleStable σ (U.comap B.mulVecLin) := by
  have hmap : (U.comap B.mulVecLin).map B.mulVecLin = U :=
    Submodule.map_comap_eq_self hUB
  refine ⟨hU.1.comap hB, ?_, ?_⟩
  · intro h
    apply hU.2.1
    rw [← hmap, h, Submodule.map_bot]
  · intro V hV hVU
    have hVU' : V.map B.mulVecLin ≤ U := by
      rw [← hmap]
      exact Submodule.map_mono hVU
    have hVeq : (V.map B.mulVecLin).comap B.mulVecLin = V :=
      Submodule.comap_map_eq_of_injective hBi V
    rcases hU.2.2 _ (hV.map hB) hVU' with h | h
    · left
      rw [← hVeq, h, Submodule.comap_bot, LinearMap.ker_eq_bot.mpr hBi]
    · right
      rw [← hVeq, h]

/-- (c) ⇒ (b): if every simple stable subspace of codimension one has a stable
complement, so does every stable subspace of codimension one. -/
theorem hasComplement_of_simple [IsAffineHom G.X.hom]
    (hc : ∀ (N : ℕ) (ρ : MatrixRepresentation G (Fin N)) (W : Submodule k (Fin N → k)),
      IsSimpleStable ρ W → Module.finrank k W + 1 = N →
        ∃ W', ρ.IsStableSubspace W' ∧ IsCompl W W') :
    ∀ (N : ℕ) (ρ : MatrixRepresentation G (Fin N)) (W : Submodule k (Fin N → k)),
      ρ.IsStableSubspace W → Module.finrank k W + 1 = N →
        ∃ W', ρ.IsStableSubspace W' ∧ IsCompl W W' := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro ρ W hW hdim
  by_cases hW0 : W = ⊥
  · subst hW0
    exact ⟨⊤, isStableSubspace_top ρ, isCompl_bot_top⟩
  obtain ⟨U, hU, hUW⟩ := exists_isSimpleStable_le ρ hW hW0
  obtain ⟨q⟩ := nonempty_quotientRepresentation ρ U hU.1
  have hker : LinearMap.ker q.projection.mulVecLin = U := q.ker_projection
  have hsurj := q.projection_surjective
  have hUpos : 0 < Module.finrank k U := by
    rw [Nat.pos_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
    exact hU.2.1
  have hqdim : q.dimension + Module.finrank k U = N := by
    have h := finrank_map_add_finrank_ker q.projection (X := ⊤) le_top
    rw [Submodule.map_top, LinearMap.range_eq_top.mpr hsurj, hker, finrank_top, finrank_top,
      Module.finrank_fin_fun, Module.finrank_fin_fun] at h
    exact h
  have hWbdim : Module.finrank k (W.map q.projection.mulVecLin) + 1 = q.dimension := by
    have h := finrank_map_add_finrank_ker q.projection (X := W) (hker.le.trans hUW)
    rw [hker] at h
    omega
  obtain ⟨Lb, hLb, hWbLb⟩ := ih q.dimension (by omega) q.representation _
    (hW.map q.intertwines) hWbdim
  set P := Lb.comap q.projection.mulVecLin with hPdef
  have hP : ρ.IsStableSubspace P := hLb.comap q.intertwines
  have hWeq : (W.map q.projection.mulVecLin).comap q.projection.mulVecLin = W :=
    Submodule.comap_map_eq_self (hker.le.trans hUW)
  have hUP : U ≤ P := hker.ge.trans (LinearMap.ker_le_comap _)
  have hPW : P ⊓ W = U := by
    rw [hPdef, ← hWeq, ← Submodule.comap_inf, inf_comm, hWbLb.inf_eq_bot, Submodule.comap_bot,
      hker]
  have hPWtop : P ⊔ W = ⊤ := by
    have h1 : (P ⊔ W).map q.projection.mulVecLin = ⊤ := by
      rw [Submodule.map_sup, hPdef, Submodule.map_comap_eq_of_surjective hsurj, sup_comm,
        hWbLb.sup_eq_top]
    have h2 : ((P ⊔ W).map q.projection.mulVecLin).comap q.projection.mulVecLin = P ⊔ W :=
      Submodule.comap_map_eq_self (hker.le.trans (hUP.trans le_sup_left))
    rw [← h2, h1, Submodule.comap_top]
  have hPdim : Module.finrank k U + 1 = Module.finrank k P := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq P W
    rw [hPWtop, hPW, finrank_top, Module.finrank_fin_fun] at h
    omega
  obtain ⟨e, τ, B, hB, hBi, hBr, hBdim⟩ := exists_subCoordinates ρ hP
  have hU' := isSimpleStable_comap hB hBi hU (hBr ▸ hUP)
  have hU'dim : Module.finrank k (U.comap B.mulVecLin) + 1 = e := by
    rw [(Submodule.equivMapOfInjective _ hBi (U.comap B.mulVecLin)).finrank_eq,
      Submodule.map_comap_eq_self (hBr ▸ hUP), ← hBdim, hPdim]
  obtain ⟨L', hL', hUL'⟩ := hc e τ _ hU' hU'dim
  have hmapU : (U.comap B.mulVecLin).map B.mulVecLin = U :=
    Submodule.map_comap_eq_self (hBr ▸ hUP)
  have hLU : L'.map B.mulVecLin ⊓ U = ⊥ := by
    rw [← hmapU, ← Submodule.map_inf _ hBi, inf_comm, hUL'.inf_eq_bot, Submodule.map_bot]
  have hLUP : L'.map B.mulVecLin ⊔ U = P := by
    rw [← hmapU, ← Submodule.map_sup, sup_comm, hUL'.sup_eq_top, Submodule.map_top, hBr]
  have hLP : L'.map B.mulVecLin ≤ P := hLUP ▸ le_sup_left
  refine ⟨L'.map B.mulVecLin, hL'.map hB, ?_, ?_⟩
  · rw [disjoint_iff, eq_bot_iff]
    calc W ⊓ L'.map B.mulVecLin ≤ (P ⊓ W) ⊓ L'.map B.mulVecLin :=
          le_inf (le_inf (inf_le_right.trans hLP) inf_le_left) inf_le_right
      _ = L'.map B.mulVecLin ⊓ U := by rw [hPW, inf_comm]
      _ = ⊥ := hLU
  · rw [codisjoint_iff, eq_top_iff, ← hPWtop, ← hLUP]
    exact sup_le (sup_le le_sup_right (hUW.trans le_sup_left)) le_sup_left

/-! ### (b) ⇒ (a): one-dimensional representations -/

/-- Without nontrivial characters, every representation on `k¹` is trivial. -/
theorem affineMatrix_eq_one_of_fin_one
    (hX : Subsingleton (G ⟶ (Gm (Spec (CommRingCat.of k))).toGrp))
    (σ : MatrixRepresentation G (Fin 1)) (A : CommAlgCat.{u} (CommRingCat.of k))
    (x : (algSpec (CommRingCat.of k)).obj (op A) ⟶ G.X) :
    (σ.affineMatrix A x : Matrix (Fin 1) (Fin 1) A) = 1 := by
  have hline : σ.StabilizesCoordinateLine 0 := by
    intro T y
    refine ⟨Matrix.GeneralLinearGroup.det (σ.pointMatrix T y), ?_⟩
    funext i
    fin_cases i
    simp [Matrix.mulVec, dotProduct, Matrix.det_unique]
  have hχ : σ.coordinateLineRationalCharacter 0 hline = 0 :=
    Additive.toMul.injective (Subsingleton.elim _ _)
  have hpt : (σ.pointMatrix ((algSpec (CommRingCat.of k)).obj (op A)) x :
      Matrix (Fin 1) (Fin 1) Γ(((algSpec (CommRingCat.of k)).obj (op A)).left, ⊤)) 0 0 = 1 := by
    have h := congrFun (σ.coordinateLineCharacter_action 0 hline _ x) 0
    rw [hχ, characterEval_zero] at h
    simpa [Matrix.mulVec, dotProduct] using h
  let e := Corepresented.affineSectionsAlgEquiv A
  have he : ((σ.pointMatrix ((algSpec (CommRingCat.of k)).obj (op A)) x :
      Matrix (Fin 1) (Fin 1) Γ(((algSpec (CommRingCat.of k)).obj (op A)).left, ⊤)).map
        e.toRingHom) = (σ.affineMatrix A x : Matrix (Fin 1) (Fin 1) A) := by
    rw [pointMatrix_eq_affineMatrix]
    ext i j
    exact e.apply_symm_apply _
  ext i j
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0, ← he, Matrix.one_apply_eq]
  exact (congrArg e hpt).trans (map_one e)

/-- A stable line of a representation of a group without nontrivial characters consists
of fixed vectors. -/
theorem exists_fixed_of_finrank_eq_one [IsAffineHom G.X.hom]
    (hX : Subsingleton (G ⟶ (Gm (Spec (CommRingCat.of k))).toGrp))
    (σ : MatrixRepresentation G m) {L : Submodule k (m → k)} (hL : σ.IsStableSubspace L)
    (hdim : Module.finrank k L = 1) :
    ∃ v ∈ L, v ≠ 0 ∧ ∀ (A : CommAlgCat.{u} (CommRingCat.of k))
      (x : (algSpec (CommRingCat.of k)).obj (op A) ⟶ G.X),
      (σ.affineMatrix A x : Matrix m m A) *ᵥ (fun j => algebraMap k A (v j)) =
        fun j => algebraMap k A (v j) := by
  obtain ⟨e, σ₂, B, hB, hBi, hBr, hBd⟩ := exists_subCoordinates σ hL
  have he : e = 1 := hBd ▸ hdim
  subst he
  refine ⟨B *ᵥ (fun _ => 1), by rw [← hBr]; exact ⟨fun _ => 1, rfl⟩, ?_, ?_⟩
  · intro h
    have h' : B.mulVecLin (fun _ => (1 : k)) = B.mulVecLin 0 := by
      rw [map_zero]
      exact h
    have := congrFun (hBi h') 0
    simp at this
  · intro A x
    have hv : (fun j => algebraMap k A ((B *ᵥ (fun _ => (1 : k))) j)) =
        B.map (algebraMap k A) *ᵥ (fun _ => algebraMap k A 1) := by
      funext j
      exact (algebraMap k A).map_mulVec B _ j
    rw [hv, Matrix.mulVec_mulVec, ← hB A x, ← Matrix.mulVec_mulVec,
      affineMatrix_eq_one_of_fin_one hX σ₂ A x, Matrix.one_mulVec]

/-! ### (b) ⇒ (a): projections and the representation on endomorphisms -/

/-- A stable subspace has an idempotent projection matrix commuting with the action in the
sense `g P = P g P`. -/
theorem exists_stableProjection [IsAffineHom G.X.hom] (ρ : MatrixRepresentation G n)
    {W : Submodule k (n → k)} (hW : ρ.IsStableSubspace W) :
    ∃ P : Matrix n n k, (∀ v, P *ᵥ v ∈ W) ∧ (∀ w ∈ W, P *ᵥ w = w) ∧ P * P = P ∧
      ∀ (A : CommAlgCat.{u} (CommRingCat.of k))
        (x : (algSpec (CommRingCat.of k)).obj (op A) ⟶ G.X),
        (ρ.affineMatrix A x : Matrix n n A) * P.map (algebraMap k A) =
          P.map (algebraMap k A) * (ρ.affineMatrix A x : Matrix n n A) *
            P.map (algebraMap k A) := by
  obtain ⟨d, B, C, hCB, hcols, hproj⟩ := exists_subspace_split_coordinates W
  have hstable := hW.isStableCoordinates B C hcols hproj
  have hint := intertwines_restrictCoordinates ρ B C hCB hstable
  have hr := range_coordinateInclusion_eq W B C hcols hproj
  refine ⟨B * C, fun v => ?_, hproj, ?_, fun A x => ?_⟩
  · rw [← hr, ← Matrix.mulVec_mulVec]
    exact ⟨C *ᵥ v, rfl⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc C, hCB, Matrix.one_mul]
  · have e := (hint A x).symm
    have hCB' : C.map (algebraMap k A) * B.map (algebraMap k A) = 1 := by
      rw [← Matrix.map_mul, hCB, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [Matrix.map_mul]
    calc (ρ.affineMatrix A x : Matrix n n A) * (B.map (algebraMap k A) * C.map (algebraMap k A))
        = ((ρ.affineMatrix A x : Matrix n n A) * B.map (algebraMap k A)) *
            C.map (algebraMap k A) := by rw [Matrix.mul_assoc]
      _ = B.map (algebraMap k A) * (C.map (algebraMap k A) * B.map (algebraMap k A)) *
            ((restrictCoordinates ρ B C hCB hstable).affineMatrix A x : Matrix _ _ A) *
            C.map (algebraMap k A) := by rw [e, hCB', Matrix.mul_one]
      _ = B.map (algebraMap k A) * C.map (algebraMap k A) *
            ((ρ.affineMatrix A x : Matrix n n A) * B.map (algebraMap k A)) *
            C.map (algebraMap k A) := by rw [e]; simp only [Matrix.mul_assoc]
      _ = B.map (algebraMap k A) * C.map (algebraMap k A) *
            (ρ.affineMatrix A x : Matrix n n A) *
            (B.map (algebraMap k A) * C.map (algebraMap k A)) := by
        simp only [Matrix.mul_assoc]

omit [DecidableEq n] in
/-- A linear functional applied entrywise commutes with left multiplication by a constant
matrix. -/
theorem map_functional_const_mul {A : Type*} [CommRing A] [Algebra k A]
    (P : Matrix n n k) (X : Matrix n n A) (ℓ : A →ₗ[k] k) :
    (P.map (algebraMap k A) * X).map ℓ = P * X.map ℓ := by
  ext i j
  have hs (c : k) (a : A) : ℓ (algebraMap k A c * a) = c * ℓ a := by
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  simp only [Matrix.map_apply, Matrix.mul_apply, map_sum, hs]

omit [DecidableEq n] in
/-- A linear functional applied entrywise commutes with right multiplication by a constant
matrix. -/
theorem map_functional_mul_const {A : Type*} [CommRing A] [Algebra k A]
    (P : Matrix n n k) (X : Matrix n n A) (ℓ : A →ₗ[k] k) :
    (X * P.map (algebraMap k A)).map ℓ = X.map ℓ * P := by
  ext i j
  have hs (c : k) (a : A) : ℓ (a * algebraMap k A c) = ℓ a * c := by
    rw [mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  simp only [Matrix.map_apply, Matrix.mul_apply, map_sum, hs]

/-- The core computation: conjugating an endomorphism `M` with `P M = M` and `M P = a P`
by a matrix preserving the image of `P`, then applying a functional, keeps this shape. -/
theorem conj_shape {A : Type*} [CommRing A] [Algebra k A] (P M : Matrix n n k) (a : k)
    (g h : Matrix n n A) (hgh : g * h = 1)
    (hg : g * P.map (algebraMap k A) = P.map (algebraMap k A) * g * P.map (algebraMap k A))
    (hh : h * P.map (algebraMap k A) = P.map (algebraMap k A) * h * P.map (algebraMap k A))
    (hPM : P * M = M) (hMP : M * P = a • P) (ℓ : A →ₗ[k] k) :
    P * (g * M.map (algebraMap k A) * h).map ℓ = (g * M.map (algebraMap k A) * h).map ℓ ∧
      (g * M.map (algebraMap k A) * h).map ℓ * P = (a * ℓ 1) • P := by
  set P' := P.map (algebraMap k A) with hP'
  set M' := M.map (algebraMap k A) with hM'
  have hPM' : P' * M' = M' := by rw [hP', hM', ← Matrix.map_mul, hPM]
  have hMP' : M' * P' = a • P' := by
    rw [hP', hM', ← Matrix.map_mul, hMP]
    ext i j
    rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
      map_mul, Algebra.smul_def]
  have e1 : g * M' = P' * (g * M') :=
    calc g * M' = g * (P' * M') := by rw [hPM']
      _ = (P' * g * P') * M' := by rw [← hg, Matrix.mul_assoc]
      _ = P' * (g * M') := by rw [Matrix.mul_assoc, Matrix.mul_assoc, hPM']
  have e2 : g * M' * h * P' = a • P' :=
    calc g * M' * h * P' = g * (M' * (h * P')) := by simp only [Matrix.mul_assoc]
      _ = g * (M' * (P' * h * P')) := by rw [hh]
      _ = g * ((M' * P') * h * P') := by simp only [Matrix.mul_assoc]
      _ = g * ((a • P') * h * P') := by rw [hMP']
      _ = a • (g * (P' * h * P')) := by simp only [Matrix.smul_mul, Matrix.mul_smul]
      _ = a • (g * (h * P')) := by rw [hh]
      _ = a • P' := by rw [← Matrix.mul_assoc, hgh, Matrix.one_mul]
  refine ⟨?_, ?_⟩
  · rw [← map_functional_const_mul, ← Matrix.mul_assoc, ← e1]
  · rw [← map_functional_mul_const, e2]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, hP', smul_eq_mul, map_smul,
      Algebra.algebraMap_eq_smul_one, smul_eq_mul]
    ring

/-- The matrix of a vector indexed by pairs, as a linear map. -/
def unvec : (n × n → k) →ₗ[k] Matrix n n k where
  toFun f := Matrix.of fun i j => f (i, j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype n] [DecidableEq n] in
@[simp] theorem unvec_apply (f : n × n → k) (i j : n) : unvec f i j = f (i, j) := rfl

/-- `W₁`: endomorphisms with image in the image of `P` that vanish on it. -/
def endW (P : Matrix n n k) : Submodule k (n × n → k) :=
  LinearMap.ker ((LinearMap.mulLeft k P - LinearMap.id) ∘ₗ unvec) ⊓
    LinearMap.ker (LinearMap.mulRight k P ∘ₗ unvec)

/-- `V₁`: endomorphisms with image in the image of `P` that are scalar on it. -/
def endV (P : Matrix n n k) : Submodule k (n × n → k) :=
  LinearMap.ker ((LinearMap.mulLeft k P - LinearMap.id) ∘ₗ unvec) ⊓
    (k ∙ P).comap (LinearMap.mulRight k P ∘ₗ unvec)

theorem mem_endW (P : Matrix n n k) (f : n × n → k) :
    f ∈ endW P ↔ P * unvec f = unvec f ∧ unvec f * P = 0 := by
  simp [endW, sub_eq_zero]

theorem mem_endV (P : Matrix n n k) (f : n × n → k) :
    f ∈ endV P ↔ P * unvec f = unvec f ∧ ∃ a : k, a • P = unvec f * P := by
  simp [endV, sub_eq_zero, Submodule.mem_span_singleton]

/-- The representation on endomorphisms acts by conjugation. -/
theorem tensorDual_mulVec (ρ : MatrixRepresentation G n)
    (A : CommAlgCat.{u} (CommRingCat.of k))
    (x : (algSpec (CommRingCat.of k)).obj (op A) ⟶ G.X) (F : n × n → A) (i j : n) :
    (((ρ.tensor ρ.dual).affineMatrix A x : Matrix (n × n) (n × n) A) *ᵥ F) (i, j) =
      ((ρ.affineMatrix A x : Matrix n n A) * Matrix.of (fun a b => F (a, b)) *
        ((ρ.affineMatrix A x)⁻¹ : GL n A).val) i j := by
  simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.of_apply,
    Fintype.sum_prod_type, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  rw [tensor_affineMatrix_entry, dual_affineMatrix, GeneralLinear.matrixContragredient_coe,
    Matrix.transpose_apply]
  ring

/-! ### (b) ⇒ (a) -/

/-- If every stable subspace of codimension one of every representation has a stable
complement, then every stable subspace has a stable complement. -/
theorem hasComplement_of_codimOne [IsAffineHom G.X.hom]
    (hX : Subsingleton (G ⟶ (Gm (Spec (CommRingCat.of k))).toGrp))
    (hb : ∀ (N : ℕ) (ρ : MatrixRepresentation G (Fin N)) (W : Submodule k (Fin N → k)),
      ρ.IsStableSubspace W → Module.finrank k W + 1 = N →
        ∃ W', ρ.IsStableSubspace W' ∧ IsCompl W W')
    (ρ : MatrixRepresentation G n) (W : Submodule k (n → k)) (hW : ρ.IsStableSubspace W) :
    ∃ W', ρ.IsStableSubspace W' ∧ IsCompl W W' := by
  by_cases hW0 : W = ⊥
  · subst hW0
    exact ⟨⊤, isStableSubspace_top ρ, isCompl_bot_top⟩
  obtain ⟨P, hPW, hPfix, hPP, hPg⟩ := exists_stableProjection ρ hW
  have hP0 : P ≠ 0 := by
    intro h
    apply hW0
    rw [eq_bot_iff]
    intro w hw
    rw [Submodule.mem_bot, ← hPfix w hw, h, Matrix.zero_mulVec]
  -- the representation on endomorphisms acts by conjugation
  set τ := ρ.tensor ρ.dual with hτdef
  have hgh : ∀ (A : CommAlgCat.{u} (CommRingCat.of k))
      (x : (algSpec (CommRingCat.of k)).obj (op A) ⟶ G.X),
      (ρ.affineMatrix A x : Matrix n n A) * ((ρ.affineMatrix A x)⁻¹ : GL n A).val = 1 :=
    fun A x => (ρ.affineMatrix A x).mul_inv
  have hPh : ∀ (A : CommAlgCat.{u} (CommRingCat.of k))
      (x : (algSpec (CommRingCat.of k)).obj (op A) ⟶ G.X),
      ((ρ.affineMatrix A x)⁻¹ : GL n A).val * P.map (algebraMap k A) =
        P.map (algebraMap k A) * ((ρ.affineMatrix A x)⁻¹ : GL n A).val *
          P.map (algebraMap k A) := by
    intro A x
    rw [← map_inv (ρ.affineMatrix A) x]
    exact hPg A x⁻¹
  have hτvec : ∀ (A : CommAlgCat.{u} (CommRingCat.of k))
      (x : (algSpec (CommRingCat.of k)).obj (op A) ⟶ G.X) (f : n × n → k) (ℓ : A →ₗ[k] k),
      unvec (fun p => ℓ (((τ.affineMatrix A x : Matrix (n × n) (n × n) A) *ᵥ
        (fun q => algebraMap k A (f q))) p)) =
      ((ρ.affineMatrix A x : Matrix n n A) * (unvec f).map (algebraMap k A) *
        ((ρ.affineMatrix A x)⁻¹ : GL n A).val).map ℓ := by
    intro A x f ℓ
    ext i j
    exact congrArg ℓ (tensorDual_mulVec ρ A x _ i j)
  have hV : τ.IsStableSubspace (endV P) := by
    intro A x f hf ℓ
    rw [mem_endV] at hf ⊢
    obtain ⟨h1, a, h2⟩ := hf
    obtain ⟨k1, k2⟩ := conj_shape P (unvec f) a _ _ (hgh A x) (hPg A x) (hPh A x) h1 h2.symm ℓ
    rw [hτvec]
    exact ⟨k1, a * ℓ 1, k2.symm⟩
  have hWs : τ.IsStableSubspace (endW P) := by
    intro A x f hf ℓ
    rw [mem_endW] at hf ⊢
    obtain ⟨h1, h2⟩ := hf
    obtain ⟨k1, k2⟩ := conj_shape P (unvec f) 0 _ _ (hgh A x) (hPg A x) (hPh A x) h1
      (by rw [h2, zero_smul]) ℓ
    rw [hτvec]
    refine ⟨k1, ?_⟩
    rw [k2, zero_mul, zero_smul]
  -- `V₁ = W₁ ⊕ k P`
  set vP : n × n → k := fun p => P p.1 p.2 with hvP
  have hunvP : unvec vP = P := rfl
  have hvP0 : vP ≠ 0 := by
    intro h
    apply hP0
    rw [← hunvP, h, map_zero]
  have hWV : endW P ≤ endV P := by
    intro f hf
    rw [mem_endW] at hf
    rw [mem_endV]
    exact ⟨hf.1, 0, by rw [hf.2, zero_smul]⟩
  have hsup : endW P ⊔ (k ∙ vP) = endV P := by
    apply le_antisymm
    · apply sup_le hWV
      rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, mem_endV, hunvP]
      exact ⟨hPP, 1, by rw [one_smul, hPP]⟩
    · intro f hf
      rw [mem_endV] at hf
      obtain ⟨h1, a, h2⟩ := hf
      rw [Submodule.mem_sup]
      refine ⟨f - a • vP, ?_, a • vP,
        Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), sub_add_cancel _ _⟩
      rw [mem_endW, map_sub, map_smul, hunvP]
      refine ⟨?_, ?_⟩
      · rw [Matrix.mul_sub, Matrix.mul_smul, hPP, h1]
      · rw [Matrix.sub_mul, Matrix.smul_mul, hPP, ← h2, sub_self]
  have hinf : endW P ⊓ (k ∙ vP) = ⊥ := by
    rw [eq_bot_iff]
    rintro f ⟨hfW, hfs⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hfs
    rw [SetLike.mem_coe, mem_endW, map_smul, hunvP, Matrix.smul_mul, hPP] at hfW
    rw [Submodule.mem_bot]
    rcases smul_eq_zero.mp hfW.2 with hc | hc
    · rw [hc, zero_smul]
    · exact absurd hc hP0
  have hdimV : Module.finrank k (endW P) + 1 = Module.finrank k (endV P) := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (endW P) (k ∙ vP)
    rw [hsup, hinf, finrank_bot, finrank_span_singleton hvP0] at h
    omega
  -- coordinates on `V₁` and the hypothesis (b)
  obtain ⟨d, σ, B, hB, hBi, hBr, hBd⟩ := exists_subCoordinates τ hV
  have hWr : endW P ≤ LinearMap.range B.mulVecLin := by
    rw [hBr]
    exact hWV
  have hW'dim : Module.finrank k ((endW P).comap B.mulVecLin) + 1 = d := by
    rw [(Submodule.equivMapOfInjective _ hBi ((endW P).comap B.mulVecLin)).finrank_eq,
      Submodule.map_comap_eq_self hWr, ← hBd, hdimV]
  obtain ⟨L, hL, hWL⟩ := hb d σ _ (hWs.comap hB) hW'dim
  have hLdim : Module.finrank k L = 1 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq ((endW P).comap B.mulVecLin) L
    rw [hWL.sup_eq_top, hWL.inf_eq_bot, finrank_top, finrank_bot,
      Module.finrank_fin_fun] at h
    omega
  obtain ⟨v, hvL, hv0, hvfix⟩ := exists_fixed_of_finrank_eq_one hX σ hL hLdim
  -- the invariant endomorphism `M₀`
  set f₀ := B *ᵥ v with hf₀
  have hf₀V : f₀ ∈ endV P := by
    rw [← hBr]
    exact ⟨v, rfl⟩
  have hf₀W : f₀ ∉ endW P := by
    intro h
    apply hv0
    have hv : v ∈ (endW P).comap B.mulVecLin ⊓ L := Submodule.mem_inf.mpr ⟨h, hvL⟩
    rwa [hWL.inf_eq_bot, Submodule.mem_bot] at hv
  have hf₀fix : ∀ (A : CommAlgCat.{u} (CommRingCat.of k))
      (x : (algSpec (CommRingCat.of k)).obj (op A) ⟶ G.X),
      (τ.affineMatrix A x : Matrix (n × n) (n × n) A) *ᵥ (fun q => algebraMap k A (f₀ q)) =
        fun q => algebraMap k A (f₀ q) := by
    intro A x
    have hv' : (fun q => algebraMap k A (f₀ q)) =
        B.map (algebraMap k A) *ᵥ (fun j => algebraMap k A (v j)) := by
      funext q
      exact (algebraMap k A).map_mulVec B v q
    rw [hv', Matrix.mulVec_mulVec, ← hB A x, ← Matrix.mulVec_mulVec, hvfix A x]
  set M₀ := unvec f₀ with hM₀
  have hM₀int : Intertwines ρ ρ M₀ := by
    intro A x
    have hconj : (ρ.affineMatrix A x : Matrix n n A) * M₀.map (algebraMap k A) *
        ((ρ.affineMatrix A x)⁻¹ : GL n A).val = M₀.map (algebraMap k A) := by
      ext i j
      have h := congrFun (hf₀fix A x) (i, j)
      rw [tensorDual_mulVec] at h
      exact h
    calc M₀.map (algebraMap k A) * (ρ.affineMatrix A x : Matrix n n A)
        = (ρ.affineMatrix A x : Matrix n n A) * M₀.map (algebraMap k A) *
            (((ρ.affineMatrix A x)⁻¹ : GL n A).val *
              (ρ.affineMatrix A x : Matrix n n A)) := by
          rw [← Matrix.mul_assoc, hconj]
      _ = (ρ.affineMatrix A x : Matrix n n A) * M₀.map (algebraMap k A) := by
          rw [(ρ.affineMatrix A x).inv_mul, Matrix.mul_one]
  obtain ⟨hPM₀, a, ha⟩ := (mem_endV P f₀).mp hf₀V
  rw [← hM₀] at hPM₀ ha
  have ha0 : a ≠ 0 := by
    intro h
    apply hf₀W
    rw [mem_endW]
    exact ⟨hPM₀, by rw [← ha, h, zero_smul]⟩
  have hMM : M₀ * M₀ = a • M₀ := by
    calc M₀ * M₀ = M₀ * (P * M₀) := by rw [hPM₀]
      _ = (M₀ * P) * M₀ := (Matrix.mul_assoc _ _ _).symm
      _ = a • M₀ := by rw [← ha, Matrix.smul_mul, hPM₀]
  -- its kernel is a stable complement
  refine ⟨(⊥ : Submodule k (n → k)).comap M₀.mulVecLin,
    (isStableSubspace_bot ρ).comap hM₀int, ?_, ?_⟩
  · rw [disjoint_iff, eq_bot_iff]
    rintro w ⟨hwW, hwK⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, Submodule.mem_bot, Matrix.mulVecLin_apply] at hwK
    rw [Submodule.mem_bot]
    have hMw : M₀ *ᵥ w = a • w :=
      calc M₀ *ᵥ w = M₀ *ᵥ (P *ᵥ w) := by rw [hPfix w hwW]
        _ = a • (P *ᵥ w) := by rw [Matrix.mulVec_mulVec, ← ha, Matrix.smul_mulVec]
        _ = a • w := by rw [hPfix w hwW]
    rw [hMw] at hwK
    exact (smul_eq_zero.mp hwK).resolve_left ha0
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    rw [Submodule.mem_sup]
    refine ⟨a⁻¹ • (M₀ *ᵥ v), ?_, v - a⁻¹ • (M₀ *ᵥ v), ?_, by abel⟩
    · apply Submodule.smul_mem
      rw [← hPM₀, ← Matrix.mulVec_mulVec]
      exact hPW _
    · rw [Submodule.mem_comap, Submodule.mem_bot, Matrix.mulVecLin_apply, Matrix.mulVec_sub,
        Matrix.mulVec_smul, Matrix.mulVec_mulVec, hMM, Matrix.smul_mulVec, smul_smul,
        inv_mul_cancel₀ ha0, one_smul, sub_self]

end Langlands.GroupScheme.SemisimpleRepresentationCodimensionOne

namespace Langlands.GroupScheme

open SemisimpleRepresentationCodimensionOne in
/-- **For a group without characters, semisimplicity is tested on submodules of codimension
one** (Milne, *Algebraic Groups* (2017), Lemma 22.40). -/
theorem semisimpleRepresentationCodimensionOne :
    SemisimpleRepresentationCodimensionOneStatement.{u} := by
  intro k _ G _ _ hX
  dsimp only
  tfae_have 1 → 2 := fun ha N ρ W hW hdim =>
    hasComplement_of_sSup_eq_top ρ (ha N ρ) W hW hdim
  tfae_have 2 → 3 := fun hb N ρ W hW hdim => hb N ρ W hW.1 hdim
  tfae_have 3 → 2 := hasComplement_of_simple
  tfae_have 2 → 1 := fun hb N ρ =>
    sSup_eq_top_of_hasComplement ρ (fun W hW => hasComplement_of_codimOne hX hb ρ W hW)
  tfae_finish

end Langlands.GroupScheme
