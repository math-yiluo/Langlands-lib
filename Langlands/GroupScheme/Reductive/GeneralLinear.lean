import Langlands.GroupScheme.Reductive.Basic
import Mathlib.LinearAlgebra.Matrix.ElementaryRowOperations
import Langlands.GroupScheme.GeneralLinearLocalization
import Mathlib.AlgebraicGeometry.Properties
import Langlands.GroupScheme.GeneralLinearSmoothProof
import Langlands.GroupScheme.Multiplicative

/-! # The unipotent radical of `GL_n` over a field is trivial

Milne, *Algebraic groups* (2017), Lemma 19.16 and Example 19.19: a normal unipotent subgroup `N`
of `GL_n` fixes a nonzero vector of the standard representation; the fixed space is stable under
`GL_n(k)` by normality, hence everything, so `N` is trivial.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme

section LinearAlgebra

variable {K : Type*} [Field K] {n : Type} [Fintype n] [DecidableEq n]

/-- A nonzero subspace of `Kⁿ` stable under `GL_n(K)` is everything. -/
theorem eq_top_of_forall_GL_mulVec_mem (W : Submodule K (n → K))
    (hW : ∀ g : GL n K, ∀ w ∈ W, (g : Matrix n n K) *ᵥ w ∈ W) (h0 : W ≠ ⊥) : W = ⊤ := by
  obtain ⟨v, hvW, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  obtain ⟨p, hp⟩ : ∃ p, v p ≠ 0 := by
    by_contra h
    push Not at h
    exact hv0 (funext h)
  have htv : ∀ q r : n, q ≠ r → ∀ x ∈ W, Pi.single q (x r) ∈ W := by
    intro q r hqr x hx
    have h := W.sub_mem (hW (Matrix.GeneralLinearGroup.transvection q r hqr 1) x hx) hx
    convert h using 1
    show _ = Matrix.transvection q r (1 : K) *ᵥ x - x
    rw [Matrix.transvection, Matrix.add_mulVec,
      Matrix.one_mulVec, add_sub_cancel_left]
    ext i
    rw [Matrix.mulVec, dotProduct]
    by_cases hi : i = q
    · subst hi
      simp [Matrix.single_apply]
    · have hqi : ¬q = i := fun h => hi h.symm
      simp [hi, hqi]
  have hne : ∀ q, q ≠ p → Pi.single q (1 : K) ∈ W := by
    intro q hq
    have h := W.smul_mem (v p)⁻¹ (htv q p hq v hvW)
    rwa [← Pi.single_smul, smul_eq_mul, inv_mul_cancel₀ hp] at h
  have hall : ∀ q, Pi.single q (1 : K) ∈ W := by
    intro q
    by_cases hq : q = p
    · subst hq
      by_cases hr : ∃ r, r ≠ q
      · obtain ⟨r, hr⟩ := hr
        have h := htv q r hr.symm _ (hne r hr)
        rwa [Pi.single_eq_same] at h
      · push Not at hr
        have hv : v = Pi.single q (v q) := by
          funext r
          rw [hr r, Pi.single_eq_same]
        have hvW' : Pi.single q (v q) ∈ W := by
          rw [← hv]
          exact hvW
        have h := W.smul_mem (v q)⁻¹ hvW'
        rwa [← Pi.single_smul, smul_eq_mul, inv_mul_cancel₀ hp] at h
    · exact hne q hq
  rw [eq_top_iff]
  intro x _
  have hx : x = ∑ i, x i • Pi.single i (1 : K) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hx]
  exact W.sum_mem fun i _ => W.smul_mem _ (hall i)

end LinearAlgebra

section Radical

variable {K : Type u} [Field K] {n : Type} [Fintype n] [DecidableEq n]

/-- The constant point of `GL_n` over a test scheme `T` given by a matrix over `K`. -/
def GeneralLinear.constantMatrixPoint (T : Over (Spec (CommRingCat.of K))) (g : GL n K) :
    T ⟶ (GeneralLinear.groupScheme n (CommRingCat.of K)).X :=
  (GeneralLinear.pointsEquiv n _ T).symm (Matrix.GeneralLinearGroup.map (scalarMap T) g)

/-- `GL_n(K)` permutes the fixed vectors of a normal subgroup of `GL_n`. -/
theorem mulVec_mem_fixedSubmodule {H : GroupScheme (Spec (CommRingCat.of K))}
    (i : H ⟶ GeneralLinear.groupScheme n (CommRingCat.of K))
    (hN : (SubgroupFunctor.range i).IsNormal) (g : GL n K) {v : n → K}
    (hv : v ∈ MatrixRepresentation.fixedSubmodule i) :
    (g : Matrix n n K) *ᵥ v ∈ MatrixRepresentation.fixedSubmodule i := by
  intro T h
  obtain ⟨h', hh'⟩ := SubgroupFunctor.mem_range.1
    (hN T (GeneralLinear.constantMatrixPoint T g)⁻¹ (h ≫ i.hom.hom) trivial
      (SubgroupFunctor.mem_range.2 ⟨h, rfl⟩))
  have key := hv T h'
  rw [MatrixRepresentation.pointMatrix_apply, hh', map_mul, map_mul, map_inv, inv_inv] at key
  rw [MatrixRepresentation.pointMatrix_apply]
  have hg : (fun j => scalarMap T (((g : Matrix n n K) *ᵥ v) j)) =
      ((GeneralLinear.pointsEquiv n _ T (GeneralLinear.constantMatrixPoint T g) :
        GL n Γ(T.left, ⊤)) : Matrix n n Γ(T.left, ⊤)) *ᵥ (fun j => scalarMap T (v j)) := by
    funext j
    rw [RingHom.map_mulVec, GeneralLinear.constantMatrixPoint, MulEquiv.apply_symm_apply]
    rfl
  rw [hg]
  set G := GeneralLinear.pointsEquiv n _ T (GeneralLinear.constantMatrixPoint T g)
  set M := GeneralLinear.pointsEquiv n _ T (h ≫ i.hom.hom)
  have e1 : (M : Matrix n n Γ(T.left, ⊤)) *ᵥ ((G : Matrix n n Γ(T.left, ⊤)) *ᵥ
      (fun j => scalarMap T (v j))) = (G : Matrix n n Γ(T.left, ⊤)) *ᵥ
        (((G⁻¹ * M * G : GL n Γ(T.left, ⊤)) : Matrix n n Γ(T.left, ⊤)) *ᵥ
          (fun j => scalarMap T (v j))) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul]
    congr 2
    group
  rw [e1, key]

variable (K n) in
/-- Milne, Lemma 19.16 and Example 19.19: every unipotent normal subgroup of `GL_n` over a field
is trivial. In particular `GL_n` has trivial unipotent radical. -/
theorem hasTrivialUnipotentRadical_generalLinear :
    HasTrivialUnipotentRadical (GeneralLinear.groupScheme n (CommRingCat.of K)) := by
  intro H i _ _ _ hU hN
  have hfix : ∀ (T : Over (Spec (CommRingCat.of K))) (h : T ⟶ H.X),
      GeneralLinear.pointsEquiv n _ T (h ≫ i.hom.hom) = 1 := by
    intro T h
    apply Units.ext
    rcases isEmpty_or_nonempty n with hn | hn
    · ext a
      exact isEmptyElim a
    obtain ⟨v, hv0, hv⟩ := hU n i
    have htop := eq_top_of_forall_GL_mulVec_mem (MatrixRepresentation.fixedSubmodule i)
      (fun g w hw => mulVec_mem_fixedSubmodule i hN g hw)
      ((Submodule.ne_bot_iff _).2 ⟨v, hv, hv0⟩)
    ext a b
    have hb : Pi.single b (1 : K) ∈ MatrixRepresentation.fixedSubmodule i := by
      rw [htop]
      exact Submodule.mem_top
    have hb' := hb T h
    have hs : (fun j => scalarMap T ((Pi.single b (1 : K) : n → K) j)) = Pi.single b 1 := by
      funext j
      by_cases hj : j = b
      · subst hj
        simp
      · simp [hj]
    rw [hs, Matrix.mulVec_single_one, MatrixRepresentation.pointMatrix_apply] at hb'
    have := congrFun hb' a
    by_cases hab : a = b
    · subst hab
      simpa [Matrix.col] using this
    · simpa [Matrix.col, hab, Matrix.one_apply_ne hab] using this
  apply SubgroupFunctor.ext
  intro T
  ext x
  rw [SubgroupFunctor.bot_carrier, Subgroup.mem_bot]
  constructor
  · intro hx
    obtain ⟨h, rfl⟩ := SubgroupFunctor.mem_range.1 hx
    apply (GeneralLinear.pointsEquiv n _ T).injective
    rw [hfix, map_one]
  · rintro rfl
    exact Subgroup.one_mem _

end Radical

section Connected

variable (K : Type u) [Field K] (n : Type) [Fintype n] [DecidableEq n]

theorem determinantPolynomial_ne_zero : GeneralLinear.determinantPolynomial n K ≠ 0 := by
  intro h
  have h1 := congrArg (MvPolynomial.eval fun p : n × n => (1 : Matrix n n K) p.1 p.2) h
  rw [GeneralLinear.determinantPolynomial, RingHom.map_det, map_zero] at h1
  have h2 : (MvPolynomial.eval fun p : n × n => (1 : Matrix n n K) p.1 p.2).mapMatrix
      (GeneralLinear.matrixVariables n K) = 1 := by
    ext i j
    simp [GeneralLinear.matrixVariables]
  rw [h2, Matrix.det_one] at h1
  exact one_ne_zero h1

instance isDomain_coordinateRing : IsDomain (GeneralLinear.CoordinateRing n K) := by
  have : IsDomain (GeneralLinear.DeterminantLocalization n K) :=
    IsLocalization.Away.isDomain (S := GeneralLinear.DeterminantLocalization n K)
      (determinantPolynomial_ne_zero K n)
  exact MulEquiv.isDomain _ (GeneralLinear.determinantLocalizationEquiv n K).toMulEquiv

/-- `GL_n` over a field is connected: its coordinate ring is a domain. -/
instance connectedSpace_generalLinear :
    ConnectedSpace (GeneralLinear.groupScheme n (CommRingCat.of K)).X.left := by
  change ConnectedSpace (Spec (CommRingCat.of (GeneralLinear.CoordinateRing n (CommRingCat.of K))))
  have : IsDomain (CommRingCat.of (GeneralLinear.CoordinateRing n (CommRingCat.of K))) :=
    isDomain_coordinateRing K n
  infer_instance

end Connected

section Iso

variable {k : Type u} [Field k]

/-- A trivial unipotent radical transfers along isomorphisms of group schemes. -/
theorem HasTrivialUnipotentRadical.of_iso {G G' : GroupScheme (Spec (CommRingCat.of k))}
    (e : G ≅ G') (h : HasTrivialUnipotentRadical G') : HasTrivialUnipotentRadical G := by
  intro H i hC hS hCon hU hN
  have hC' : IsClosedSubgroup (i ≫ e.hom) := by
    unfold IsClosedSubgroup at hC ⊢
    rw [Grp.comp_hom_hom, Over.comp_left]
    have : IsIso e.hom.hom.hom.left := by
      have : IsIso e.hom.hom.hom :=
        ⟨⟨e.inv.hom.hom, by rw [← Grp.comp_hom_hom, e.hom_inv_id]; rfl,
          by rw [← Grp.comp_hom_hom, e.inv_hom_id]; rfl⟩⟩
      exact (inferInstance : IsIso ((Over.forget _).map e.hom.hom.hom))
    infer_instance
  have hN' : (SubgroupFunctor.range (i ≫ e.hom)).IsNormal := by
    intro T g' x' _ hx'
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.1 hx'
    have hg' : g' = (g' ≫ e.inv.hom.hom) ≫ e.hom.hom.hom := by
      rw [Category.assoc, ← Grp.comp_hom_hom, e.inv_hom_id]
      rfl
    obtain ⟨z, hz⟩ := SubgroupFunctor.mem_range.1 (hN T (g' ≫ e.inv.hom.hom) (y ≫ i.hom.hom)
      trivial (SubgroupFunctor.mem_range.2 ⟨y, rfl⟩))
    refine SubgroupFunctor.mem_range.2 ⟨z, ?_⟩
    rw [Grp.comp_hom_hom, ← Category.assoc, hz, MonObj.mul_comp, MonObj.mul_comp,
      GrpObj.inv_comp, ← hg', Category.assoc]
  have h' := h H (i ≫ e.hom) hC' hS hCon hU hN'
  apply SubgroupFunctor.ext
  intro T
  ext x
  rw [SubgroupFunctor.bot_carrier, Subgroup.mem_bot]
  constructor
  · intro hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.1 hx
    have hy : y ≫ (i ≫ e.hom).hom.hom ∈ (SubgroupFunctor.range (i ≫ e.hom)).carrier T :=
      SubgroupFunctor.mem_range.2 ⟨y, rfl⟩
    rw [h', SubgroupFunctor.bot_carrier, Subgroup.mem_bot, Grp.comp_hom_hom, ← Category.assoc] at hy
    have := congrArg (· ≫ e.inv.hom.hom) hy
    simp only [Category.assoc, MonObj.one_comp] at this
    rwa [← Grp.comp_hom_hom, e.hom_inv_id, Grp.id_hom_hom, Category.comp_id] at this
  · rintro rfl
    exact Subgroup.one_mem _

end Iso

section BaseChange

variable (n : Type) [Fintype n] [DecidableEq n] {R R' : CommRingCat.{u}} (b : Spec R' ⟶ Spec R)

/-- Points of the base change of `GL_n` along `Spec R' ⟶ Spec R` are invertible matrices. -/
def GeneralLinear.baseChangeGLPointsEquiv (T : Over (Spec R')) :
    (T ⟶ ((GroupScheme.baseChange b).obj (GeneralLinear.groupScheme n R)).X) ≃*
      (T ⟶ (GeneralLinear.groupScheme n R').X) :=
  (baseChangePointsEquiv b (GeneralLinear.groupScheme n R) T).trans
    ((GeneralLinear.pointsEquiv n R ((Over.map b).obj T)).trans
      (GeneralLinear.pointsEquiv n R' T).symm)

theorem GeneralLinear.baseChangeGLPointsEquiv_naturality {T T' : Over (Spec R')} (a : T' ⟶ T)
    (x : T ⟶ ((GroupScheme.baseChange b).obj (GeneralLinear.groupScheme n R)).X) :
    GeneralLinear.baseChangeGLPointsEquiv n b T' (a ≫ x) =
      a ≫ GeneralLinear.baseChangeGLPointsEquiv n b T x := by
  apply (GeneralLinear.pointsEquiv n R' T').injective
  simp only [GeneralLinear.baseChangeGLPointsEquiv, MulEquiv.trans_apply,
    MulEquiv.apply_symm_apply, baseChangePointsEquiv_naturality,
    GeneralLinear.pointsEquiv_naturality]
  rfl

/-- The base change of `GL_n` along `Spec R' ⟶ Spec R` is `GL_n` over `R'`. -/
def GeneralLinear.baseChangeIso :
    (GroupScheme.baseChange b).obj (GeneralLinear.groupScheme n R) ≅
      GeneralLinear.groupScheme n R' :=
  isoOfPoints (GeneralLinear.baseChangeGLPointsEquiv n b)
    (GeneralLinear.baseChangeGLPointsEquiv_naturality n b)

end BaseChange

section Main

variable {k : Type u} [Field k]

theorem isIso_left_of_iso {S : Scheme.{u}} {G G' : GroupScheme S} (e : G ≅ G') :
    IsIso e.hom.hom.hom.left := by
  have : IsIso e.hom.hom.hom :=
    ⟨⟨e.inv.hom.hom, by rw [← Grp.comp_hom_hom, e.hom_inv_id]; rfl,
      by rw [← Grp.comp_hom_hom, e.inv_hom_id]; rfl⟩⟩
  exact (inferInstance : IsIso ((Over.forget _).map e.hom.hom.hom))

/-- Pseudo-reductivity transfers along isomorphisms of group schemes. -/
theorem IsPseudoReductive.of_iso {G G' : GroupScheme (Spec (CommRingCat.of k))} (e : G ≅ G')
    (h : IsPseudoReductive G') : IsPseudoReductive G := by
  have hw : G.X.hom = e.hom.hom.hom.left ≫ G'.X.hom := (Over.w e.hom.hom.hom).symm
  have := isIso_left_of_iso e
  have := h.smooth
  have := h.isAffineHom
  have := h.connectedSpace
  refine ⟨?_, ?_, ?_, HasTrivialUnipotentRadical.of_iso e h.hasTrivialUnipotentRadical⟩
  · rw [hw]
    infer_instance
  · rw [hw]
    infer_instance
  · let φ := Scheme.homeoOfIso (asIso e.hom.hom.hom.left)
    exact φ.symm.surjective.connectedSpace φ.symm.continuous

variable (k) (n : Type) [Fintype n] [DecidableEq n]

/-- `GL_n` over a field is pseudo-reductive: smooth, affine, connected, with trivial
`k`-unipotent radical. -/
theorem isPseudoReductive_generalLinear :
    IsPseudoReductive (GeneralLinear.groupScheme n (CommRingCat.of k)) where
  smooth := GeneralLinear.smoothStatement n (CommRingCat.of k)
  isAffineHom := GeneralLinear.isAffineHom_groupScheme (n := n) (R := CommRingCat.of k)
  connectedSpace := connectedSpace_generalLinear k n
  hasTrivialUnipotentRadical := hasTrivialUnipotentRadical_generalLinear k n

/-- `GL_n` over a field is a connected reductive group. -/
theorem isConnectedReductive_generalLinear :
    IsConnectedReductive (GeneralLinear.groupScheme n (CommRingCat.of k)) where
  smooth := GeneralLinear.smoothStatement n (CommRingCat.of k)
  isAffineHom := GeneralLinear.isAffineHom_groupScheme (n := n) (R := CommRingCat.of k)
  connectedSpace := connectedSpace_generalLinear k n
  hasTrivialGeometricUnipotentRadical :=
    HasTrivialUnipotentRadical.of_iso (GeneralLinear.baseChangeIso n (toAlgebraicClosure k))
      (hasTrivialUnipotentRadical_generalLinear (AlgebraicClosure k) n)

/-- `GL_n` over every commutative ring is a reductive group scheme. -/
theorem isReductive_generalLinear (R : CommRingCat.{u}) :
    IsReductive (GeneralLinear.groupScheme n R) where
  smooth := GeneralLinear.smoothStatement n R
  isAffineHom := inferInstance
  geometricFiber s :=
    IsPseudoReductive.of_iso (GeneralLinear.baseChangeIso n (geometricPoint (Spec R) s))
      (isPseudoReductive_generalLinear _ n)

end Main

end Langlands.GroupScheme
