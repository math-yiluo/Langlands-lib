import Langlands.GroupScheme.Reductive.CharZeroSemisimplicity.TangentStability
import Langlands.GroupScheme.Reductive.CharZeroSemisimplicity.FlagBasis
import Langlands.GroupScheme.Dynamic.UnitriangularEmbedding
import Langlands.GroupScheme.Dynamic.Conjugation
import Langlands.GroupScheme.UnitriangularUnipotentProof
import Langlands.GroupScheme.UnipotentClosedSubgroupProof
import Langlands.GroupScheme.Reductive.RadicalFieldExtension.RationalSide
import Langlands.GroupScheme.Rational.TorusWeightRepresentative
import Langlands.GroupScheme.Reductive.Basic
import Langlands.Algebra.NilpotentStableFlag

/-! # Tangent vectors in a nilpotent normalized family are trivial -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry Module
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  {n : Type} [Fintype n] [DecidableEq n]

/-- Membership of an affine point in the inverse image of a block unipotent subgroup. -/
theorem mem_comap_blockUnipotent_affine (σ : MatrixRepresentation G n) (e : n → ℤ)
    (A : CommAlgCat.{u} (CommRingCat.of k))
    (x : (algSpec (CommRingCat.of k)).obj (op A) ⟶ G.X) :
    x ∈ ((GeneralLinear.blockUnipotent n (CommRingCat.of k) e).comap σ).carrier _ ↔
      ∀ i j, e i ≤ e j →
        (σ.affineMatrix A x : Matrix n n A) i j = (1 : Matrix n n A) i j := by
  rw [SubgroupFunctor.mem_comap, GeneralLinear.mem_blockUnipotent,
    GeneralLinear.pointsEquiv_eq_affinePointsEquiv]
  have hinj : Function.Injective (Corepresented.affineSectionsIso A).inv.hom := by
    intro a b hab
    have hleft (a : A) : (Corepresented.affineSectionsIso A).hom.hom
        ((Corepresented.affineSectionsIso A).inv.hom a) = a :=
      ConcreteCategory.congr_hom (Corepresented.affineSectionsIso A).inv_hom_id a
    exact (hleft a).symm.trans ((congrArg _ hab).trans (hleft b))
  refine forall_congr' fun i => forall_congr' fun j => imp_congr_right fun _ => ?_
  change (Corepresented.affineSectionsIso A).inv.hom _ = _ ↔ _
  by_cases hij : i = j
  · subst hij
    rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
    exact ⟨fun h => hinj (h.trans (map_one _).symm), fun h => h ▸ map_one _⟩
  · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij]
    exact ⟨fun h => hinj (h.trans (map_zero _).symm), fun h => h ▸ map_zero _⟩

omit [DecidableEq n] in
/-- The coordinate matrix of a basis sends a vector to its coordinates. -/
theorem basisCoordinateGL_mulVec [DecidableEq n] (b : Basis n k (n → k)) (v : n → k) :
    (basisCoordinateGL b : Matrix n n k) *ᵥ v = b.repr v := by
  change b.toMatrix (Pi.basisFun k n) *ᵥ v = _
  have h := (Pi.basisFun k n).toMatrix_mulVec_repr b v
  rwa [show ((Pi.basisFun k n).repr v : n → k) = v from
    funext fun i => by simp] at h

/-- The tangent matrices of the conjugate by a basis-coordinate point are the
tangent endomorphisms written in that basis. -/
theorem conjugate_basisCoordinatePoint_tangentMatrix_apply (ρ : MatrixRepresentation G n)
    (b : Basis n k (n → k)) (Y : lieKernel G k) (i j : n) :
    (ρ.conjugate (basisCoordinatePoint b)).tangentMatrix k Y i j =
      b.repr (Matrix.toLin' (ρ.tangentMatrix k Y) (b j)) i := by
  have hc := (intertwines_conjugate_basisCoordinatePoint ρ b).tangentMatrix Y
  have hbj : (basisCoordinateGL b : Matrix n n k) *ᵥ b j = Pi.single j 1 := by
    rw [basisCoordinateGL_mulVec, b.repr_self, Finsupp.single_eq_pi_single]
  rw [Matrix.toLin'_apply, ← basisCoordinateGL_mulVec, Matrix.mulVec_mulVec, hc,
    ← Matrix.mulVec_mulVec, hbj, Matrix.mulVec_single_one, Matrix.col_apply]

section CharZero

variable [CharZero k] [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [Smooth G.X.hom] [ConnectedSpace G.X.left]

/-- Let `σ` be a faithful closed matrix representation of a smooth connected group
in characteristic zero with trivial unipotent radical. If all tangent matrices of
`σ` are block upper triangular for the weights `e`, then a tangent vector whose
matrix is strictly block upper triangular is trivial. The inverse image of the
block unipotent subgroup is a closed normal unipotent subgroup; its identity
component is trivial by the radical hypothesis, and has the same tangent space. -/
theorem eq_one_of_tangentMatrix_blockUnipotent (hrad : HasTrivialUnipotentRadical G)
    (σ : MatrixRepresentation G n) (hσ : IsClosedSubgroup σ) (e : n → ℤ)
    (hP : ∀ (Y : lieKernel G k) i j, e i < e j → σ.tangentMatrix k Y i j = 0)
    (X : lieKernel G k) (hX : ∀ i j, e i ≤ e j → σ.tangentMatrix k X i j = 0) :
    X = 1 := by
  let N := Fintype.card n
  let jK := subgroupIntersectionFst σ (GeneralLinear.blockUnipotentHom n (CommRingCat.of k) e)
  let K := subgroupIntersection σ (GeneralLinear.blockUnipotentHom n (CommRingCat.of k) e)
  have hrep := (GeneralLinear.isRepresentedBy_blockUnipotent n (CommRingCat.of k) e)
    |>.comap_subgroupIntersectionFst
      (GeneralLinear.isClosedSubgroup_blockUnipotentHom n (CommRingCat.of k) e) σ
  have hcl := isClosedSubgroup_subgroupIntersectionFst σ
    (GeneralLinear.isClosedSubgroup_blockUnipotentHom n (CommRingCat.of k) e)
  have : IsClosedImmersion jK.hom.hom.left := hcl
  have : Mono jK.hom.hom := hrep.1
  have hA : IsAffineHom K.X.hom := by
    rw [← jK.hom.hom.w]
    infer_instance
  have hL : LocallyOfFiniteType K.X.hom := by
    rw [← jK.hom.hom.w]
    infer_instance
  have hS : Smooth K.X.hom := affineCartierSmooth k K hA hL
  -- The inverse image is unipotent: it embeds into a standard unitriangular group.
  let r := (GeneralLinear.reindexIso (GeneralLinear.antitoneEnumeration e).symm
    (CommRingCat.of k)).hom
  have hle : SubgroupFunctor.range (jK ≫ σ ≫ r) ≤
      GeneralLinear.blockUnipotent (Fin N) (CommRingCat.of k) (fun i => -(i.val : ℤ)) := by
    intro T x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    have hy : y ≫ jK.hom.hom ∈
        ((GeneralLinear.blockUnipotent n (CommRingCat.of k) e).comap σ).carrier T := by
      rw [← hrep.2]
      exact ⟨y, rfl⟩
    rw [SubgroupFunctor.mem_comap] at hy
    change GeneralLinear.pointsEquiv (Fin N) (CommRingCat.of k) T
      (y ≫ (jK ≫ σ ≫ r).hom.hom) ∈
        GeneralLinear.blockUnipotentSubgroup Γ(T.left, ⊤) (fun i : Fin N => -(i.val : ℤ))
    simp only [Grp.comp_hom_hom, ← Category.assoc]
    rw [GeneralLinear.pointsEquiv_reindexIso]
    exact GeneralLinear.matrixReindex_mem_unitriangular Γ(T.left, ⊤) e _ hy
  let H := GeneralLinear.blockUnipotentScheme (Fin N) (CommRingCat.of k)
    (fun i => -(i.val : ℤ))
  have hinc := GeneralLinear.isClosedSubgroup_blockUnipotentHom (Fin N)
    (CommRingCat.of k) (fun i => -(i.val : ℤ))
  let f : K ⟶ H := (GeneralLinear.isRepresentedBy_blockUnipotent (Fin N) (CommRingCat.of k)
    (fun i => -(i.val : ℤ))).factorHom (jK ≫ σ ≫ r) hle
  have hf : IsClosedSubgroup f := by
    apply IsClosedSubgroup.of_comp hinc
    rw [SubgroupFunctor.IsRepresentedBy.factorHom_comp]
    exact hcl.comp (hσ.comp_iso _)
  have : Smooth (GeneralLinear.groupScheme (Fin N) (CommRingCat.of k)).X.hom :=
    GeneralLinear.smoothStatement (Fin N) (CommRingCat.of k)
  have : IsClosedImmersion (GeneralLinear.blockUnipotentHom (Fin N) (CommRingCat.of k)
      (fun i => -(i.val : ℤ))).hom.hom.left := hinc
  have : IsAffineHom H.X.hom := by
    rw [← (GeneralLinear.blockUnipotentHom (Fin N) (CommRingCat.of k)
      (fun i => -(i.val : ℤ))).hom.hom.w]
    infer_instance
  have : LocallyOfFiniteType H.X.hom := by
    rw [← (GeneralLinear.blockUnipotentHom (Fin N) (CommRingCat.of k)
      (fun i => -(i.val : ℤ))).hom.hom.w]
    infer_instance
  have hKu : IsUnipotent K := unipotentClosedSubgroup k H K f hf
    (unitriangularUnipotent k N)
  -- The inverse image is normal, since the whole group lands in the block parabolic.
  have hpar := comap_blockParabolic_eq_top σ e hP
  have hnorm : (GeneralLinear.blockUnipotent n (CommRingCat.of k) e).IsNormalizedBy
      (GeneralLinear.blockParabolic n (CommRingCat.of k) e) := by
    have h := GeneralLinear.range_blockUnipotent_isNormalizedBy_range_blockParabolic n
      (CommRingCat.of k) e
    rwa [(GeneralLinear.isRepresentedBy_blockUnipotent n _ e).2,
      (GeneralLinear.isRepresentedBy_blockParabolic n _ e).2] at h
  have hN : (SubgroupFunctor.range jK).IsNormal := by
    rw [hrep.2]
    intro T g x _ hx
    have hg : g ∈ ((GeneralLinear.blockParabolic n (CommRingCat.of k) e).comap σ).carrier T := by
      rw [hpar]
      exact Subgroup.mem_top _
    rw [SubgroupFunctor.mem_comap] at hg hx ⊢
    rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp]
    exact hnorm T _ _ hg hx
  -- Its identity component is a smooth connected unipotent normal closed subgroup.
  have hj0 : IsClosedSubgroup (identityComponentι K ≫ jK) :=
    (IdentityComponent.isClosedSubgroup_identityComponentι K).comp hcl
  have hu0 : IsUnipotent (identityComponent K) :=
    unipotentClosedSubgroup k K (identityComponent K) (identityComponentι K)
      (IdentityComponent.isClosedSubgroup_identityComponentι K) hKu
  have hN0 := RadicalFieldExtension.isNormal_range_identityComponentι_comp jK hcl hN
  have hbot := hrad _ (identityComponentι K ≫ jK) hj0 inferInstance inferInstance hu0 hN0
  have hmem : Additive.ofMul X ∈ RelativeRoot.tangentSubmodule
      ((GeneralLinear.blockUnipotent n (CommRingCat.of k) e).comap σ) := by
    rw [RelativeRoot.mem_tangentSubmodule, mem_comap_blockUnipotent_affine,
      affineMatrix_eq_matrixUnit]
    intro i l hil
    change (1 + GeneralLinear.DualNumber.epsilonMatrix (σ.tangentMatrix k X)) i l =
      (1 : Matrix n n (DualNumber k)) i l
    rw [Matrix.add_apply, GeneralLinear.DualNumber.epsilonMatrix_apply, hX i l hil,
      TrivSqZeroExt.inr_zero, add_zero]
  rw [← hrep.2, ← RelativeRoot.tangentSubmodule_range_identityComponent_comp jK, hbot,
    RelativeRoot.tangentSubmodule_bot, Submodule.mem_bot] at hmem
  exact ofMul_eq_zero.mp hmem

/-- Let `σ` be a faithful closed matrix representation of a smooth connected group
in characteristic zero with trivial unipotent radical, and `A` a space of
nilpotent endomorphisms of `n → k` that consists of tangent endomorphisms of `σ`
and is normalized by all of them. Then every tangent vector whose endomorphism lies
in `A` is trivial. A flag stable under the tangent endomorphisms and moved one step
down by `A` gives a basis in which the hypotheses of
`eq_one_of_tangentMatrix_blockUnipotent` hold for the conjugated representation. -/
theorem eq_one_of_nilpotent_normalized (hrad : HasTrivialUnipotentRadical G)
    (σ : MatrixRepresentation G n) (hσ : IsClosedSubgroup σ)
    (A : Submodule k (Module.End k (n → k)))
    (hnil : ∀ a ∈ A, IsNilpotent a)
    (hsub : ∀ a ∈ A, ∃ Y : lieKernel G k, Matrix.toLin' (σ.tangentMatrix k Y) = a)
    (hbr : ∀ (Y : lieKernel G k), ∀ a ∈ A,
      Matrix.toLin' (σ.tangentMatrix k Y) * a - a * Matrix.toLin' (σ.tangentMatrix k Y) ∈ A)
    (X : lieKernel G k) (hX : Matrix.toLin' (σ.tangentMatrix k X) ∈ A) :
    X = 1 := by
  classical
  obtain ⟨F, m, hF, h0, hm, hstepA, hstepS⟩ := Langlands.Algebra.exists_stable_flag_of_isNilpotent
    A (fun a ha c hc => by
      obtain ⟨Y, rfl⟩ := hsub a ha
      exact hbr Y c hc)
    hnil (Set.range fun Y : lieKernel G k => Matrix.toLin' (σ.tangentMatrix k Y))
    (by
      rintro _ ⟨Y, rfl⟩ a ha
      exact hbr Y a ha)
  obtain ⟨b, e, hb⟩ := Langlands.LinearAlgebra.exists_basis_flag F hF h0 m hm
  have hσ' : IsClosedSubgroup (σ.conjugate (basisCoordinatePoint b)) := hσ.comp_iso _
  apply eq_one_of_tangentMatrix_blockUnipotent hrad _ hσ' (fun i => (e i : ℤ))
  · intro Y i j hij
    rw [conjugate_basisCoordinatePoint_tangentMatrix_apply]
    refine Langlands.LinearAlgebra.repr_apply_eq_zero_of_flag b e F hb _ 0
      (fun t v hv => hstepS t _ ⟨Y, rfl⟩ v hv) i j ?_
    have : e i < e j := by exact_mod_cast hij
    omega
  · intro i j hij
    rw [conjugate_basisCoordinatePoint_tangentMatrix_apply]
    refine Langlands.LinearAlgebra.repr_apply_eq_zero_of_flag b e F hb _ 1
      (fun t v hv => hstepA t _ hX v hv) i j ?_
    have : e i ≤ e j := by exact_mod_cast hij
    omega

end CharZero

end Langlands.GroupScheme.MatrixRepresentation
