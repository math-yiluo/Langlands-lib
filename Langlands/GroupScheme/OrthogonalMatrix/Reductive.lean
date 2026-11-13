import Langlands.GroupScheme.OrthogonalMatrix.Roots
import Langlands.GroupScheme.IdentityComponent.Transport

/-! # The identity component of the split orthogonal group is reductive

Over every field `K` and for `l` with at least two elements, the identity component of the split
orthogonal group `OrthogonalMatrix.groupScheme l K` has trivial unipotent radical, hence is a
connected reductive group.

The fixed vectors of a smooth connected unipotent normal subgroup of the identity component form
a nonzero subspace of `K^{l ⊕ l}` that is stable under the Levi matrices `diag(A, A⁻ᵀ)` and the
unipotent block matrices `[[1, Y], [0, 1]]`, `[[1, 0], [Y, 1]]` with `Y` alternating, all of
whose constant points lie in the identity component. Such a subspace is everything, so the
subgroup acts trivially.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Matrix
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.OrthogonalMatrix

variable {l : Type} [Fintype l] [DecidableEq l]

/-! ### Irreducibility of the standard representation -/

section Irreducible

variable {K : Type*} [Field K]

variable (K) in
/-- The alternating matrix `E_{ab} - E_{ba}`. -/
def alt (a b : l) : Matrix l l K :=
  Matrix.single a b 1 - Matrix.single b a 1

omit [Fintype l] in
theorem isAlt_alt (a b : l) : IsAlt (alt K a b) :=
  ⟨Matrix.single a b 1, by rw [alt, Matrix.transpose_single]⟩

theorem alt_mulVec_apply_left {a b : l} (hab : a ≠ b) (x : l → K) :
    (alt K a b *ᵥ x) a = x b := by
  simp [alt, Matrix.sub_mulVec, Matrix.single_mulVec, hab]

theorem alt_mulVec_single {a b : l} (hab : a ≠ b) :
    alt K a b *ᵥ Pi.single b 1 = Pi.single a 1 := by
  ext i
  by_cases hi : i = a
  · subst hi
    simp [alt, hab]
  · simp [alt, hi, Ne.symm hi, hab]

theorem upper_mulVec (Y : Matrix l l K) (v : l ⊕ l → K) :
    SymplecticMatrix.upper Y *ᵥ v = v + Sum.elim (Y *ᵥ (v ∘ Sum.inr)) (0 : l → K) := by
  ext (i | i) <;> simp [SymplecticMatrix.upper, Matrix.fromBlocks_mulVec]

theorem lower_mulVec (Y : Matrix l l K) (v : l ⊕ l → K) :
    SymplecticMatrix.lower Y *ᵥ v = v + Sum.elim (0 : l → K) (Y *ᵥ (v ∘ Sum.inl)) := by
  ext (i | i) <;> simp [SymplecticMatrix.lower, Matrix.fromBlocks_mulVec, add_comm]

theorem levi_mulVec_elim (g : GL l K) (x : l → K) :
    SymplecticMatrix.levi g *ᵥ Sum.elim x (0 : l → K) =
      Sum.elim ((g : Matrix l l K) *ᵥ x) (0 : l → K) := by
  ext (i | i) <;> simp [SymplecticMatrix.levi, Matrix.fromBlocks_mulVec]

theorem transvection_mulVec_sub (a b : l) (c : K) (y : l → K) :
    Matrix.transvection a b c *ᵥ y - y = Pi.single a (c * y b) := by
  rw [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec, add_sub_cancel_left,
    Matrix.single_mulVec]
  rfl

omit [Fintype l] in
theorem single_inl_eq (c : l) :
    (Pi.single (Sum.inl c) (1 : K) : l ⊕ l → K) = Sum.elim (Pi.single c 1) (0 : l → K) := by
  ext (i | i) <;> simp [Pi.single_apply]

omit [Fintype l] in
theorem single_inr_eq (c : l) :
    (Pi.single (Sum.inr c) (1 : K) : l ⊕ l → K) = Sum.elim (0 : l → K) (Pi.single c 1) := by
  ext (i | i) <;> simp [Pi.single_apply]

/-- **Irreducibility.** A nonzero subspace of `K^{l ⊕ l}` stable under the Levi matrices and the
unipotent block matrices with alternating blocks is everything, when `l` has at least two
elements. -/
theorem eq_top_of_stable [Nontrivial l] (W : Submodule K (l ⊕ l → K)) (hW : W ≠ ⊥)
    (hlevi : ∀ g : GL l K, ∀ v ∈ W, SymplecticMatrix.levi g *ᵥ v ∈ W)
    (hupper : ∀ Y : Matrix l l K, IsAlt Y → ∀ v ∈ W, SymplecticMatrix.upper Y *ᵥ v ∈ W)
    (hlower : ∀ Y : Matrix l l K, IsAlt Y → ∀ v ∈ W, SymplecticMatrix.lower Y *ᵥ v ∈ W) :
    W = ⊤ := by
  have hU : ∀ Y : Matrix l l K, IsAlt Y → ∀ v ∈ W,
      Sum.elim (Y *ᵥ (v ∘ Sum.inr)) (0 : l → K) ∈ W := by
    intro Y hY v hv
    have h := W.sub_mem (hupper Y hY v hv) hv
    rwa [upper_mulVec, add_sub_cancel_left] at h
  have hL : ∀ Y : Matrix l l K, IsAlt Y → ∀ v ∈ W,
      Sum.elim (0 : l → K) (Y *ᵥ (v ∘ Sum.inl)) ∈ W := by
    intro Y hY v hv
    have h := W.sub_mem (hlower Y hY v hv) hv
    rwa [lower_mulVec, add_sub_cancel_left] at h
  -- a nonzero vector of `W` supported on the first block
  obtain ⟨x, hx0, hx⟩ : ∃ x : l → K, x ≠ 0 ∧ Sum.elim x (0 : l → K) ∈ W := by
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff W).1 hW
    by_cases hr : v ∘ Sum.inr = 0
    · refine ⟨v ∘ Sum.inl, fun h => hv0 ?_, ?_⟩
      · ext (i | i)
        · exact congrFun h i
        · exact congrFun hr i
      · have e : Sum.elim (v ∘ Sum.inl) (0 : l → K) = v := by
          ext (i | i)
          · rfl
          · exact (congrFun hr i).symm
        rw [e]
        exact hv
    · obtain ⟨b, hb⟩ : ∃ b, v (Sum.inr b) ≠ 0 := by
        by_contra h
        push Not at h
        exact hr (funext h)
      obtain ⟨a, hab⟩ := exists_ne b
      refine ⟨alt K a b *ᵥ (v ∘ Sum.inr), fun h => hb ?_, hU _ (isAlt_alt a b) v hv⟩
      have h' := congrFun h a
      rw [alt_mulVec_apply_left hab, Pi.zero_apply] at h'
      exact h'
  -- transvections
  have hT : ∀ y : l → K, Sum.elim y (0 : l → K) ∈ W → ∀ a b, a ≠ b →
      Sum.elim (Pi.single a (y b)) (0 : l → K) ∈ W := by
    intro y hy a b hab
    have h := W.sub_mem (hlevi (Matrix.GeneralLinearGroup.transvection a b hab 1) _ hy) hy
    rw [levi_mulVec_elim] at h
    have e : Sum.elim (Pi.single a (y b)) (0 : l → K) =
        Sum.elim (((Matrix.GeneralLinearGroup.transvection a b hab (1 : K) : GL l K) :
          Matrix l l K) *ᵥ y) (0 : l → K) - Sum.elim y (0 : l → K) := by
      change _ = Sum.elim (Matrix.transvection a b (1 : K) *ᵥ y) (0 : l → K) - _
      ext (i | i)
      · have := congrFun (transvection_mulVec_sub a b (1 : K) y) i
        rw [Pi.sub_apply, one_mul] at this
        simp only [Sum.elim_inl, Pi.sub_apply]
        exact this.symm
      · simp
    rw [e]
    exact h
  obtain ⟨b, hb⟩ : ∃ b, x b ≠ 0 := by
    by_contra h
    push Not at h
    exact hx0 (funext h)
  have hne : ∀ c, c ≠ b → Sum.elim (Pi.single c (1 : K)) (0 : l → K) ∈ W := by
    intro c hcb
    have h := W.smul_mem (x b)⁻¹ (hT x hx c b hcb)
    have e : Sum.elim (Pi.single c (1 : K)) (0 : l → K) =
        (x b)⁻¹ • Sum.elim (Pi.single c (x b)) (0 : l → K) := by
      ext (i | i)
      · by_cases hi : i = c
        · subst hi
          simp [hb]
        · simp [hi]
      · simp
    rw [e]
    exact h
  have hall : ∀ c, Sum.elim (Pi.single c (1 : K)) (0 : l → K) ∈ W := by
    intro c
    by_cases hcb : c = b
    · subst hcb
      obtain ⟨a, hac⟩ := exists_ne c
      have h := hT _ (hne a hac) c a (Ne.symm hac)
      rw [Pi.single_eq_same] at h
      exact h
    · exact hne c hcb
  have hbasis : ∀ z : l ⊕ l, Pi.single z (1 : K) ∈ W := by
    rintro (c | c)
    · rw [single_inl_eq]
      exact hall c
    · obtain ⟨b', hb'⟩ := exists_ne c
      have h := hL (alt K c b') (isAlt_alt c b') _ (hall b')
      rw [Sum.elim_comp_inl, alt_mulVec_single (Ne.symm hb')] at h
      rw [single_inr_eq]
      exact h
  rw [eq_top_iff, ← (Pi.basisFun K (l ⊕ l)).span_eq, Submodule.span_le]
  rintro _ ⟨z, rfl⟩
  rw [Pi.basisFun_apply]
  exact hbasis z

end Irreducible

/-! ### Fixed vectors of normal subgroups of the identity component -/

section Radical

variable {K : Type u} [Field K]

local notation "𝐆" => groupScheme l (CommRingCat.of K)

/-- If conjugation by the constant point of `g` preserves the points of `H`, then `g` preserves
the fixed vectors of `H` in the standard representation. -/
theorem mulVec_mem_fixedSubmodule {H : GroupScheme (Spec (CommRingCat.of K))} (j : H ⟶ 𝐆)
    (g : orthogonalGroup l K)
    (hN : ∀ (T : Over (Spec (CommRingCat.of K))) (h : T ⟶ H.X), ∃ h' : T ⟶ H.X,
      h' ≫ j.hom.hom = (constantPoint T g)⁻¹ * (h ≫ j.hom.hom) * constantPoint T g)
    {v : l ⊕ l → K}
    (hv : v ∈ MatrixRepresentation.fixedSubmodule (j ≫ inclusion l (CommRingCat.of K))) :
    (g : Matrix (l ⊕ l) (l ⊕ l) K) *ᵥ v ∈
      MatrixRepresentation.fixedSubmodule (j ≫ inclusion l (CommRingCat.of K)) := by
  intro T h
  obtain ⟨h', hh'⟩ := hN T h
  have key := hv T h'
  rw [MatrixRepresentation.pointMatrix_apply, Grp.comp_hom_hom, ← Category.assoc,
    pointsEquiv_inclusion, hh'] at key
  simp only [map_mul, map_inv] at key
  rw [MatrixRepresentation.pointMatrix_apply, Grp.comp_hom_hom, ← Category.assoc,
    pointsEquiv_inclusion]
  have hg : (fun i => scalarMap T (((g : Matrix (l ⊕ l) (l ⊕ l) K) *ᵥ v) i)) =
      ((pointsEquiv l _ T (constantPoint T g) : orthogonalGroup l Γ(T.left, ⊤)) :
        Matrix (l ⊕ l) (l ⊕ l) Γ(T.left, ⊤)) *ᵥ (fun i => scalarMap T (v i)) := by
    funext i
    rw [RingHom.map_mulVec, pointsEquiv_constantPoint]
    rfl
  rw [hg]
  set G := toGL (pointsEquiv l _ T (constantPoint T g))
  set M := toGL (pointsEquiv l _ T (h ≫ j.hom.hom))
  have e1 : (M : Matrix (l ⊕ l) (l ⊕ l) Γ(T.left, ⊤)) *ᵥ
      ((G : Matrix (l ⊕ l) (l ⊕ l) Γ(T.left, ⊤)) *ᵥ (fun i => scalarMap T (v i))) =
      (G : Matrix (l ⊕ l) (l ⊕ l) Γ(T.left, ⊤)) *ᵥ
        (((G⁻¹ * M * G : GL (l ⊕ l) Γ(T.left, ⊤)) : Matrix (l ⊕ l) (l ⊕ l) Γ(T.left, ⊤)) *ᵥ
          (fun i => scalarMap T (v i))) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul]
    congr 2
    group
  change (M : Matrix (l ⊕ l) (l ⊕ l) Γ(T.left, ⊤)) *ᵥ
    ((G : Matrix (l ⊕ l) (l ⊕ l) Γ(T.left, ⊤)) *ᵥ (fun i => scalarMap T (v i))) =
      (G : Matrix (l ⊕ l) (l ⊕ l) Γ(T.left, ⊤)) *ᵥ (fun i => scalarMap T (v i))
  rw [e1, key]

/-- A unipotent group whose points are normalized by the constant points of the identity
component acts trivially. -/
theorem pointsEquiv_eq_one [Nontrivial l] {H : GroupScheme (Spec (CommRingCat.of K))}
    (j : H ⟶ 𝐆) (hU : IsUnipotent H)
    (hN : ∀ g : orthogonalGroup l K,
      (∀ T, constantPoint T g ∈ (SubgroupFunctor.range (identityComponentι 𝐆)).carrier T) →
      ∀ (T : Over (Spec (CommRingCat.of K))) (h : T ⟶ H.X), ∃ h' : T ⟶ H.X,
        h' ≫ j.hom.hom = (constantPoint T g)⁻¹ * (h ≫ j.hom.hom) * constantPoint T g)
    (T : Over (Spec (CommRingCat.of K))) (h : T ⟶ H.X) :
    pointsEquiv l _ T (h ≫ j.hom.hom) = 1 := by
  apply ext
  intro a b
  let ρ := j ≫ inclusion l (CommRingCat.of K)
  obtain ⟨v, hv0, hv⟩ := hU (l ⊕ l) ρ
  have hstab : ∀ g : orthogonalGroup l K,
      (∀ T, constantPoint T g ∈ (SubgroupFunctor.range (identityComponentι 𝐆)).carrier T) →
      ∀ w ∈ MatrixRepresentation.fixedSubmodule ρ,
        (g : Matrix (l ⊕ l) (l ⊕ l) K) *ᵥ w ∈ MatrixRepresentation.fixedSubmodule ρ :=
    fun g hg w hw => mulVec_mem_fixedSubmodule j g (hN g hg) hw
  have htop := eq_top_of_stable (MatrixRepresentation.fixedSubmodule ρ)
    ((Submodule.ne_bot_iff _).2 ⟨v, hv, hv0⟩)
    (fun g w hw => hstab (leviHom K g) (fun T => constantPoint_levi_mem T g) w hw)
    (fun Y hY w hw => hstab ⟨_, upper_mem hY⟩ (fun T => constantPoint_upper_mem T hY) w hw)
    (fun Y hY w hw => hstab ⟨_, lower_mem hY⟩ (fun T => constantPoint_lower_mem T hY) w hw)
  have hb : Pi.single b (1 : K) ∈ MatrixRepresentation.fixedSubmodule ρ := by
    rw [htop]
    exact Submodule.mem_top
  have hb' := hb T h
  have hs : (fun i => scalarMap T ((Pi.single b (1 : K) : l ⊕ l → K) i)) = Pi.single b 1 := by
    funext i
    by_cases hi : i = b
    · subst hi
      simp
    · simp [hi]
  rw [hs, Matrix.mulVec_single_one, MatrixRepresentation.pointMatrix_apply] at hb'
  change _ = _ at hb'
  dsimp only [ρ] at hb'
  rw [Grp.comp_hom_hom, ← Category.assoc, pointsEquiv_inclusion] at hb'
  have := congrFun hb' a
  by_cases hab : a = b
  · subst hab
    simpa [Matrix.col] using this
  · simpa [Matrix.col, hab, Matrix.one_apply_ne hab] using this

variable (l K) in
/-- **Trivial unipotent radical.** Every smooth connected unipotent normal closed subgroup of the
identity component of the split orthogonal group over a field is trivial, when `l` has two
elements. -/
theorem hasTrivialUnipotentRadical_identityComponent [Nontrivial l] :
    HasTrivialUnipotentRadical (identityComponent 𝐆) := by
  intro H i _ _ _ hU hN
  have hm : Mono (identityComponentι 𝐆).hom.hom := by
    rw [IdentityComponent.identityComponentι_hom_hom]
    infer_instance
  have hconj : ∀ g : orthogonalGroup l K,
      (∀ T, constantPoint T g ∈ (SubgroupFunctor.range (identityComponentι 𝐆)).carrier T) →
      ∀ (T : Over (Spec (CommRingCat.of K))) (h : T ⟶ H.X), ∃ h' : T ⟶ H.X,
        h' ≫ (i ≫ identityComponentι 𝐆).hom.hom =
          (constantPoint T g)⁻¹ * (h ≫ (i ≫ identityComponentι 𝐆).hom.hom) *
            constantPoint T g := by
    intro g hg T h
    obtain ⟨c, hc⟩ := SubgroupFunctor.mem_range.1 (hg T)
    obtain ⟨h', hh'⟩ := SubgroupFunctor.mem_range.1
      (hN T c⁻¹ (h ≫ i.hom.hom) trivial (SubgroupFunctor.mem_range.2 ⟨h, rfl⟩))
    refine ⟨h', ?_⟩
    rw [Grp.comp_hom_hom, ← Category.assoc, hh', inv_inv, MonObj.mul_comp,
      MonObj.mul_comp, GrpObj.inv_comp, hc, Category.assoc]
  apply SubgroupFunctor.ext
  intro T
  ext x
  rw [SubgroupFunctor.bot_carrier, Subgroup.mem_bot]
  constructor
  · intro hx
    obtain ⟨h, rfl⟩ := SubgroupFunctor.mem_range.1 hx
    apply (cancel_mono (identityComponentι 𝐆).hom.hom).1
    rw [Category.assoc, MonObj.one_comp]
    apply (pointsEquiv l _ T).injective
    have h1 := pointsEquiv_eq_one (i ≫ identityComponentι 𝐆) hU hconj T h
    rw [Grp.comp_hom_hom] at h1
    rw [h1, map_one]
  · rintro rfl
    exact Subgroup.one_mem _

variable (l K) in
/-- **Reductivity.** The identity component of the split orthogonal group over a field is a
connected reductive group, when `l` has at least two elements. -/
theorem isConnectedReductive_identityComponent [Nontrivial l] :
    IsConnectedReductive (identityComponent 𝐆) where
  smooth := inferInstance
  isAffineHom := inferInstance
  connectedSpace := inferInstance
  hasTrivialGeometricUnipotentRadical :=
    HasTrivialUnipotentRadical.of_iso
      (IdentityComponent.baseChangeIso 𝐆 (algebraMap K (AlgebraicClosure K)))
      (HasTrivialUnipotentRadical.of_iso
        (IdentityComponent.mapIso (baseChangeModelIso l (toAlgebraicClosure K)))
        (hasTrivialUnipotentRadical_identityComponent l (AlgebraicClosure K)))

end Radical

end Langlands.GroupScheme.OrthogonalMatrix
