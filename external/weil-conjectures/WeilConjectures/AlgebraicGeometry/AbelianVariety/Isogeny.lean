/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Basic
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Cube
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Projective
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Basic
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Image

/-!
# The multiplication-by-`n` isogeny

Multiplication by `n` on an abelian variety `A` of dimension `g` is a finite flat surjective
homomorphism, hence an isogeny, of degree `n ^ (2 * g)`, and its kernel `A[n]` is a finite flat
group scheme of that order. On points over an algebraically closed field it is surjective, so
`A(K)` is a divisible group.

Multiplication by `n` is written `𝟙 A ^ n`, the `n`-th power of the identity in the group
`A ⟶ A` coming from `CategoryTheory.GrpObj.Hom.group`.

## Main statements

- `AlgebraicGeometry.locallyQuasiFinite_npow_id_of_isAlgClosed`: over an algebraically closed
  field, multiplication by `n` has finite fibres.
- `AlgebraicGeometry.isFinite_npow_id`, `AlgebraicGeometry.surjective_npow_id`: multiplication
  by `n` is finite and surjective.
- `AlgebraicGeometry.IsIsogeny.isFinite`, `AlgebraicGeometry.IsIsogeny.flat`,
  `AlgebraicGeometry.IsIsogeny.finrank_eq`: an isogeny is finite flat of degree the order of
  its kernel.
- `AlgebraicGeometry.IsIsogeny.isFiniteLocallyFreeOfDegree`: an isogeny of abelian varieties is
  finite locally free of degree the order of its kernel.
- `AlgebraicGeometry.isIsogeny_npow_id`, `AlgebraicGeometry.isogenyDegree_npow_id`:
  multiplication by `n` is an isogeny of degree `n ^ (2 * g)`.
- `AlgebraicGeometry.finrank_npow_id`: multiplication by `n` is finite locally free of rank
  `n ^ (2 * g)`.
- `AlgebraicGeometry.isFiniteLocallyFreeOfDegree_npow_id`,
  `AlgebraicGeometry.singleton_mem_fppfPrecoverage_npow_id`: multiplication by `n` is finite
  locally free of degree `n ^ (2 * g)`, and an fppf covering.
- `AlgebraicGeometry.isFinite_torsionSubgroupScheme`,
  `AlgebraicGeometry.flat_torsionSubgroupScheme`,
  `AlgebraicGeometry.finrankΓ_torsionSubgroupScheme`: `A[n]` is finite flat of order
  `n ^ (2 * g)`.
- `AlgebraicGeometry.surjective_npow_points`: `A(K)` is divisible.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

variable {K : Type u} [Field K]

open Scheme.Modules in
/-- Over an algebraically closed field `K`, multiplication by `0 < n` on an abelian variety `A`
is locally quasi-finite. This is the main step of blueprint `proposition-multiplication-n--2`.

Let `N = L ⊗ [-1]^* L` for an ample invertible `L`; it is ample and symmetric, so
`[n]^* N ≅ N^{⊗ n²}`. If `[n]` is not quasi-finite at some point, it is not quasi-finite at some
closed point `x`, as the quasi-finite locus is open. The fibre `F` of `[n]` over the closed point
`y = [n] x` is then not discrete at `x`, so it has positive (and finite) dimension and contains a
closed subscheme `C` of dimension one, proper over `K`. On `C` the map `[n]` factors through
`Spec κ(y)`, so `(N|_C)^{⊗ n²} ≅ ([n]^* N)|_C` is trivial; but `N|_C` is ample, which is
impossible on a proper curve over an algebraically closed field. -/
theorem locallyQuasiFinite_npow_id_of_isAlgClosed [IsAlgClosed K] (A : Over (Spec (.of K)))
    [GrpObj A] [IsAbelianVariety A] (n : ℕ) (hn : 0 < n) :
    LocallyQuasiFinite (𝟙 A ^ n).left := by
  set f := (𝟙 A ^ n).left
  -- A symmetric ample module `N` with `[n]^* N ≅ N^{⊗ n²}`.
  obtain ⟨L, hL⟩ := IsAbelianVariety.exists_isAmple A
  have hLinv := hL.isInvertible
  have : L.symmetrisation.IsInvertible :=
    inferInstanceAs (Scheme.Modules.tensorObj L (overPullback ι[A] L)).IsInvertible
  have hN := IsAbelianVariety.isAmple_symmetrisation A L hL
  obtain ⟨eN⟩ := nonempty_iso_overPullback_npow_id A L.symmetrisation
    (IsAbelianVariety.nonempty_iso_overPullback_inv_symmetrisation A L) n
  have : IsProper f := by
    have : IsProper (f ≫ A.hom) := (Over.w (𝟙 A ^ n)).symm ▸ inferInstance
    exact IsProper.of_comp f A.hom
  rw [← f.quasiFiniteLocus_eq_top_iff]
  by_contra hne
  -- A closed point `x` at which `f` is not quasi-finite; its image `y = f x` is closed.
  have := QuasiCompact.compactSpace_of_compactSpace A.hom
  obtain ⟨x, hx, hxc⟩ := f.quasiFiniteLocus.isOpen.isClosed_compl.exists_closed_singleton <| by
    by_contra h
    exact hne (eq_top_iff.mpr fun z _ ↦ by_contra fun hz ↦ h ⟨z, hz⟩)
  have hy : IsClosed {f x} := by simpa using f.isClosedMap _ hxc
  have : IsClosedImmersion (A.left.fromSpecResidueField (f x)) :=
    isClosed_singleton_iff_isClosedImmersion.mp hy
  have : IsClosedImmersion (f.fiberι (f x)) :=
    inferInstanceAs (IsClosedImmersion (pullback.fst _ _))
  -- The fibre over `y` has finite positive dimension, since `x` is not isolated in it.
  have hx' : ¬ IsOpen {f.asFiber x} := by
    rwa [← Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber, ← f.mem_quasiFiniteLocus]
  have : LocallyOfFiniteType (f.fiberToSpecResidueField (f x)) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd _ _))
  have := LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField (f x))
  have h1 : 1 ≤ topologicalKrullDim (f.fiber (f x)) := by
    by_contra h
    have := IsLocallyArtinian.of_topologicalKrullDim_le_zero (Order.le_of_lt_succ (not_le.mp h))
    exact hx' (isOpen_discrete _)
  have htop : topologicalKrullDim (f.fiber (f x)) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_
      (f.fiberι (f x)).isClosedEmbedding.isInducing.topologicalKrullDim_le
    rw [IsAbelianVariety.topologicalKrullDim_eq]
    exact_mod_cast ENat.natCast_ne_top _
  -- A proper curve `C` in the fibre, on which `N` restricts to an ample module.
  obtain ⟨C, i, hi, hC⟩ := Scheme.exists_isClosedImmersion_topologicalKrullDim_eq_one h1 htop
  let j := i ≫ f.fiberι (f x)
  have : IsProper (j ≫ A.hom) := inferInstanceAs (IsProper (i ≫ f.fiberι (f x) ≫ A.hom))
  have hN' : IsAmple (j ≫ A.hom) ((Scheme.Modules.pullback j).obj L.symmetrisation) :=
    hN.pullback j
  -- `[n]` is constant on `C`, so `(N|_C)^{⊗ n²} ≅ ([n]^* N)|_C` is trivial.
  have hj : j ≫ f =
      (i ≫ f.fiberToSpecResidueField (f x)) ≫ A.left.fromSpecResidueField (f x) := by
    simp [j, Scheme.Hom.fiber_fac]
  obtain ⟨eT⟩ := IsInvertible.nonempty_iso_unit
    (IsLocalRing.closedPoint (A.left.residueField (f x)))
    ((Scheme.Modules.pullback (A.left.fromSpecResidueField (f x))).obj L.symmetrisation)
  obtain ⟨e₁⟩ := nonempty_pullback_tensorPow_iso j L.symmetrisation (n ^ 2)
  have e : ((Scheme.Modules.pullback j).obj L.symmetrisation).tensorPow (n ^ 2) ≅
      𝟙_ C.Modules :=
    e₁.symm ≪≫ (Scheme.Modules.pullback j).mapIso eN.symm ≪≫ (pullbackComp j f).app _ ≪≫
      (pullbackCongr hj).app _ ≪≫ ((pullbackComp _ _).app _).symm ≪≫
      (Scheme.Modules.pullback _).mapIso eT ≪≫ pullbackObjUnitIso _
  exact (hN'.isEmpty_tensorPow_iso_unit hC (pow_pos hn 2)).false e

open scoped Obj in
/-- Blueprint `proposition-multiplication-n--2`: Finiteness of the fibres of the multiplication map.

Let `A` be an abelian variety over `K` and `0 < n`. Then `[n] : A ⟶ A` is finite.

This is also blueprint `proposition-multiplication-n--2`. Since `[n]` is proper, it suffices that it
is locally quasi-finite. Its base change to an algebraic closure `K̄` of `K` is multiplication by
`n` on the abelian variety `A_K̄`, which is locally quasi-finite by
`AlgebraicGeometry.locallyQuasiFinite_npow_id_of_isAlgClosed`, and local quasi-finiteness
descends along the surjection `A_K̄ ⟶ A`. -/
theorem isFinite_npow_id (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A] (n : ℕ)
    (hn : 0 < n) :
    IsFinite (𝟙 A ^ n).left := by
  have : IsProper (𝟙 A ^ n).left := by
    have : IsProper ((𝟙 A ^ n).left ≫ A.hom) := (Over.w (𝟙 A ^ n)).symm ▸ inferInstance
    exact IsProper.of_comp _ A.hom
  let g : Spec (.of (AlgebraicClosure K)) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))
  have hφ : (Over.pullback g).map (𝟙 A ^ n) = 𝟙 ((Over.pullback g).obj A) ^ n := by
    rw [← (Over.pullback g).homMonoidHom_apply, map_pow]
    simp
  have : LocallyQuasiFinite ((Over.pullback g).map (𝟙 A ^ n)).left :=
    hφ ▸ locallyQuasiFinite_npow_id_of_isAlgClosed _ n hn
  -- The base change of `[n]` along `A_K̄ ⟶ A` is `[n]` on `A_K̄`.
  have hsq : IsPullback (pullback.fst A.hom g) ((Over.pullback g).map (𝟙 A ^ n)).left
      (𝟙 A ^ n).left (pullback.fst A.hom g) := by
    refine IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm (IsPullback.of_hasPullback A.hom g)
    convert IsPullback.of_hasPullback A.hom g using 1
    · exact Over.w ((Over.pullback g).map (𝟙 A ^ n))
    · exact Over.w (𝟙 A ^ n)
  have := LocallyQuasiFinite.of_isPullback_of_surjective hsq
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

/-- Blueprint `proposition-multiplication-n--2`: Finiteness of the fibres of the multiplication map.

The kernel `A[n] = ker [n]` of multiplication by `0 < n` on an abelian variety is a finite
group scheme: it is the base change of the finite morphism `[n]` along the unit section. -/
theorem isFinite_torsionSubgroupScheme (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A]
    (n : ℕ) (hn : 0 < n) :
    IsFinite (torsionSubgroupScheme A n).hom :=
  have := isFinite_npow_id A n hn
  MorphismProperty.of_isPullback ((GrpObj.isPullback_kerι (𝟙 A ^ n)).map (Over.forget _)) this

/-- Blueprint `proposition-multiplication-n--1`: Surjectivity of the multiplication map.

Let `A` be an abelian variety over `K` and `0 < n`. Then `[n] : A ⟶ A` is surjective, so `A` is
a divisible group scheme.

This is also blueprint `proposition-multiplication-n--1`, whose finiteness half is
`AlgebraicGeometry.isFinite_torsionSubgroupScheme`. The scheme-theoretic image `Z` of `[n]` is a
closed subscheme of `A` onto which `[n]` maps surjectively
(`AlgebraicGeometry.exists_isMonHom_imageι`). As `A ⟶ Z` is finite and surjective,
`dim Z = dim A`; a closed subset of the irreducible finite-dimensional `A` of full dimension is
all of `A`. -/
theorem surjective_npow_id (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A] (n : ℕ)
    (hn : 0 < n) :
    Surjective (𝟙 A ^ n).left := by
  have := isFinite_npow_id A n hn
  have := irreducibleSpace_of_connectedSpace A
  let f := (𝟙 A ^ n).left
  obtain ⟨-, hsurj, -⟩ := exists_isMonHom_imageι (𝟙 A ^ n)
  have : IsProper (f.toImage ≫ f.imageι ≫ A.hom) := by
    rw [f.toImage_imageι_assoc, Over.w (𝟙 A ^ n)]; infer_instance
  have : IsProper f.toImage := .of_comp _ (f.imageι ≫ A.hom)
  have : LocallyQuasiFinite (f.toImage ≫ f.imageι) := by
    rw [f.toImage_imageι]; infer_instance
  have : LocallyQuasiFinite f.toImage := .of_comp _ f.imageι
  have hι := f.imageι.isClosedEmbedding.isInducing.surjective_of_topologicalKrullDim_eq
    f.imageι.isClosedEmbedding.isClosed_range (by
      rw [IsAbelianVariety.topologicalKrullDim_eq]
      exact WithBot.coe_injective.ne (ENat.natCast_ne_top _))
    f.toImage.topologicalKrullDim_eq_of_surjective.symm
  have : Surjective (f.toImage ≫ f.imageι) := ⟨by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp]; exact hι.comp hsurj.surj⟩
  rwa [f.toImage_imageι] at this

/-- Blueprint `proposition-multiplication-n--1`: Surjectivity of the multiplication map.

The `n`-torsion of an abelian variety is zero-dimensional for `0 < n`: it is finite over `K`
(`AlgebraicGeometry.isFinite_torsionSubgroupScheme`), so its underlying space is discrete. -/
theorem topologicalKrullDim_torsionSubgroupScheme (A : Over (Spec (.of K))) [GrpObj A]
    [IsAbelianVariety A] (n : ℕ) (hn : 0 < n) :
    topologicalKrullDim (torsionSubgroupScheme A n).left = 0 := by
  have := isFinite_torsionSubgroupScheme A n hn
  obtain ⟨p⟩ : Nonempty (Spec (.of K)) := inferInstance
  have : DiscreteTopology (torsionSubgroupScheme A n).left := by
    rw [← isDiscrete_univ_iff]
    convert (torsionSubgroupScheme A n).hom.isDiscrete_preimage_singleton p
    exact (Set.eq_univ_of_forall fun _ ↦ Subsingleton.elim _ _).symm
  let x := (η[torsionSubgroupScheme A n]).left p
  have : Nonempty (TopologicalSpace.IrreducibleCloseds (torsionSubgroupScheme A n).left) :=
    ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  exact le_antisymm (topologicalKrullDim_zero_of_discreteTopology _) Order.krullDim_nonneg

variable {A B : Over (Spec (.of K))} [GrpObj A] [GrpObj B]

/-- Translation identifies the fibres of a homomorphism `f : A ⟶ B` of group schemes with its
kernel: for a point `x : Spec Ω ⟶ A`, the fibre of `f` over `x ≫ f` is the base change
`ker f ×_K Spec Ω`, embedded into `A` by `(k, t) ↦ k + x t`. -/
theorem exists_isPullback_kernel (f : A ⟶ B) [IsMonHom f] {Ω : CommRingCat.{u}}
    (x : Spec Ω ⟶ A.left) :
    ∃ φ : pullback (GrpObj.ker f).hom (x ≫ A.hom) ⟶ A.left,
      IsPullback φ (pullback.snd (GrpObj.ker f).hom (x ≫ A.hom)) f.left (x ≫ f.left) :=
  ⟨_, (GrpObj.isPullback_ker_tensor f (Over.homMk x rfl : Over.mk (x ≫ A.hom) ⟶ A)).map
    (Over.forget _)⟩

/-- The fibres of an isogeny are finite: the fibre over `f a` is the image of the finite scheme
`ker f ×_K Spec κ(a)` under translation by the `κ(a)`-point `a`. -/
theorem IsIsogeny.finite_preimage_singleton (f : A ⟶ B) [IsIsogeny f] (y : B.left) :
    (f.left ⁻¹' {y}).Finite := by
  obtain ⟨a, rfl⟩ := f.left.surjective y
  let x := A.left.fromSpecResidueField a
  let z : Spec (A.left.residueField a) := IsLocalRing.closedPoint _
  obtain ⟨φ, H⟩ := exists_isPullback_kernel f x
  have : Finite (pullback (C := Scheme) (GrpObj.ker f).hom (x ≫ A.hom)) := by
    refine Set.finite_univ_iff.mp (((pullback.snd (GrpObj.ker f).hom
      (x ≫ A.hom)).finite_preimage_singleton z).subset fun w _ ↦ ?_)
    exact Subsingleton.elim (α := Spec (A.left.residueField a)) _ _
  refine (Set.finite_range φ).subset fun a' (ha' : f.left a' = f.left a) ↦ ?_
  obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := f.left) (g := x ≫ f.left)
    a' z (by rw [ha', Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply])
  exact ⟨H.isoPullback.inv w, by rw [← Scheme.Hom.comp_apply, H.isoPullback_inv_fst, hw]⟩

/-- All fibres of an isogeny `f` have degree the order of its kernel: by
`AlgebraicGeometry.exists_isPullback_kernel` the fibre over `f a`, base changed to `κ(a)`, is
the kernel base changed to `κ(a)`, and the fibre degree is invariant under base change. -/
theorem IsIsogeny.fiberDegree_eq (f : A ⟶ B) [IsIsogeny f] [IsAffineHom f.left] (y : B.left) :
    f.left.fiberDegree y = isogenyDegree f := by
  obtain ⟨a, rfl⟩ := f.left.surjective y
  let x := A.left.fromSpecResidueField a
  let z : Spec (A.left.residueField a) := IsLocalRing.closedPoint _
  obtain ⟨φ, H⟩ := exists_isPullback_kernel f x
  have hz : (x ≫ f.left) z = f.left a := by
    rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
  rw [← hz, ← Scheme.Hom.fiberDegree_of_isPullback f.left H z,
    Scheme.Hom.fiberDegree_of_isPullback (GrpObj.ker f).hom (.of_hasPullback _ _) z,
    fiberDegree_eq_finrankΓ]
  rfl

variable [IsAbelianVariety A] [IsAbelianVariety B]

omit [IsAbelianVariety B] in
/-- Blueprint `proposition-multiplication-n--1`: The degree of an isogeny is the degree of the
kernel.

An isogeny of abelian varieties is a finite morphism: it is proper, `A` being proper, and has
finite fibres (`AlgebraicGeometry.IsIsogeny.finite_preimage_singleton`). -/
theorem IsIsogeny.isFinite (f : A ⟶ B) [IsIsogeny f] : IsFinite f.left := by
  have : IsProper (f.left ≫ B.hom) := by rw [Over.w f]; infer_instance
  have : IsProper f.left := .of_comp f.left B.hom
  have := LocallyQuasiFinite.of_finite_preimage_singleton f.left
    (IsIsogeny.finite_preimage_singleton f)
  exact IsFinite.of_isProper_of_locallyQuasiFinite f.left

/-- Blueprint `proposition-multiplication-n--1`: The degree of an isogeny is the degree of the
kernel.

An isogeny of abelian varieties is a flat morphism: it is finite onto the reduced scheme `B`
with all fibres of the same degree (`AlgebraicGeometry.Scheme.Hom.flat_of_fiberDegree_eq`). -/
theorem IsIsogeny.flat (f : A ⟶ B) [IsIsogeny f] : Flat f.left := by
  have := IsIsogeny.isFinite f
  have : IsReduced B.left := GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian B.hom
  have := LocallyOfFiniteType.isLocallyNoetherian B.hom
  exact f.left.flat_of_fiberDegree_eq (IsIsogeny.fiberDegree_eq f)

/-- Blueprint `proposition-multiplication-n--1`: The degree of an isogeny is the degree of the
kernel.

For an isogeny `f : A ⟶ B` of abelian varieties with kernel of order `d`, the sheaf `f_* 𝒪_A` is
locally free of rank `d`: the degree of the finite flat morphism `f` equals the order of its
kernel. -/
theorem IsIsogeny.finrank_eq (f : A ⟶ B) [IsIsogeny f] (y : B.left) :
    f.left.finrank y = isogenyDegree f := by
  have := IsIsogeny.isFinite f
  have : IsReduced B.left := GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian B.hom
  have := LocallyOfFiniteType.isLocallyNoetherian B.hom
  exact f.left.finrank_eq_of_fiberDegree_eq (IsIsogeny.fiberDegree_eq f) y

/-- Blueprint `proposition-multiplication-n--1`: The degree of an isogeny.

An isogeny `f : A ⟶ B` of abelian varieties is finite locally free of degree the order of its
kernel: it is finite (`AlgebraicGeometry.IsIsogeny.isFinite`), flat
(`AlgebraicGeometry.IsIsogeny.flat`) and of finite presentation, and all of its fibres have
degree `isogenyDegree f` (`AlgebraicGeometry.IsIsogeny.fiberDegree_eq`).

This is the second paragraph of blueprint `proposition-multiplication-n--1` (and of
`proposition-multiplication-n--1`): an isogeny of abelian varieties is finite and flat, and its
degree as a finite flat morphism is the order of its kernel. As blueprint
`proposition-multiplication-n--1` notes, this is a theorem and not part of the definition
`AlgebraicGeometry.IsIsogeny`. -/
theorem IsIsogeny.isFiniteLocallyFreeOfDegree (f : A ⟶ B) [IsIsogeny f] :
    f.left.IsFiniteLocallyFreeOfDegree (isogenyDegree f) := by
  have := IsIsogeny.isFinite f
  have := IsIsogeny.flat f
  have := LocallyOfFiniteType.isLocallyNoetherian B.hom
  have : LocallyOfFinitePresentation f.left :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  exact { fiberDegree_eq := IsIsogeny.fiberDegree_eq f }

/-- Blueprint `proposition-multiplication-n`: The multiplication-by-`n` isogeny.

Let `A` be an abelian variety over `K` and let `0 < n`. Then `[n] : A ⟶ A` is a finite flat
surjective homomorphism, hence an isogeny.

This is also blueprint `proposition-multiplication-n--1`. Multiplication by `n` is a homomorphism
since `A` is commutative (`AlgebraicGeometry.IsAbelianVariety.isCommMonObj`), it is surjective by
`AlgebraicGeometry.surjective_npow_id`, and its kernel `A[n]` is finite by
`AlgebraicGeometry.isFinite_torsionSubgroupScheme`. -/
theorem isIsogeny_npow_id (n : ℕ) (hn : 0 < n) : IsIsogeny (𝟙 A ^ n) :=
  have := surjective_npow_id A n hn
  { isFinite_ker := isFinite_torsionSubgroupScheme A n hn }

open Scheme.Modules in
/-- Blueprint `proposition-multiplication-n`: The multiplication-by-`n` isogeny.

Multiplication by `0 < n` on an abelian variety of dimension `g` has degree `n ^ (2 * g)`.

Let `N = L ⊗ [-1]^* L` for an ample invertible `L`; it is ample and symmetric, so
`[n]^* N ≅ N^{⊗ n²}` (`AlgebraicGeometry.nonempty_iso_overPullback_npow_id`). Hence
`deg_{[n]^* N}(A) = deg_{N^{⊗ n²}}(A) = n^{2g} deg_N(A)`
(`AlgebraicGeometry.Scheme.Hom.degree_tensorPow`), while
`deg_{[n]^* N}(A) = deg [n] · deg_N(A)` for the finite surjective `[n]`
(`AlgebraicGeometry.Scheme.Hom.degree_pullback`), and `deg [n]` is the order of `A[n]`
(`AlgebraicGeometry.IsIsogeny.finrank_eq`). As `deg_N(A) > 0` (Stacks 0BEV), `deg [n] = n^{2g}`.
-/
theorem isogenyDegree_npow_id (n : ℕ) (hn : 0 < n) :
    isogenyDegree (𝟙 A ^ n) = n ^ (2 * IsAbelianVariety.dim A) := by
  obtain ⟨L, hL⟩ := IsAbelianVariety.exists_isAmple A
  have hLinv := hL.isInvertible
  have : L.symmetrisation.IsInvertible :=
    inferInstanceAs (Scheme.Modules.tensorObj L (overPullback ι[A] L)).IsInvertible
  have hN := IsAbelianVariety.isAmple_symmetrisation A L hL
  obtain ⟨e⟩ := nonempty_iso_overPullback_npow_id A L.symmetrisation
    (IsAbelianVariety.nonempty_iso_overPullback_inv_symmetrisation A L) n
  have := isIsogeny_npow_id (A := A) n hn
  have := isFinite_npow_id A n hn
  have := surjective_npow_id A n hn
  have : IsReduced A.left := GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian A.hom
  have : IsIntegral A.left := isIntegral_of_irreducibleSpace_of_isReduced _
  have hpull := A.hom.degree_pullback A.hom (𝟙 A ^ n).left (Over.w _) L.symmetrisation hN
  rw [A.hom.degree_congr e, A.hom.degree_tensorPow _ hN, IsIsogeny.finrank_eq,
    ← IsAbelianVariety.dim] at hpull
  have hpos := A.hom.degree_pos_of_isAmple_of_nonempty L.symmetrisation hN
  rw [pow_mul]
  exact_mod_cast (mul_right_cancel₀ hpos.ne' hpull).symm

omit [IsAbelianVariety A] in
/-- Blueprint `proposition-multiplication-n`: The multiplication-by-`n` isogeny.

The `n`-torsion of an abelian variety is flat over the base field for `0 < n`: every scheme over
a field is flat over it. -/
theorem flat_torsionSubgroupScheme (n : ℕ) (_hn : 0 < n) :
    Flat (torsionSubgroupScheme A n).hom :=
  inferInstance

/-- Blueprint `proposition-multiplication-n`: The multiplication-by-`n` isogeny.

The `n`-torsion of an abelian variety of dimension `g` has order `n ^ (2 * g)` for `0 < n`. -/
theorem finrankΓ_torsionSubgroupScheme (n : ℕ) (hn : 0 < n) :
    (torsionSubgroupScheme A n).hom.finrankΓ = n ^ (2 * IsAbelianVariety.dim A) :=
  isogenyDegree_npow_id n hn

/-- Blueprint `proposition-multiplication-n--1`: Multiplication by `n` is finite flat of degree
`n ^ (2 * g)`.

Let `A` be an abelian variety of dimension `g` over `K` and let `0 < n`. Then `[n] : A ⟶ A` is
finite locally free of rank `n ^ (2 * g)`. Finiteness and flatness are
`AlgebraicGeometry.isFinite_npow_id` and `AlgebraicGeometry.IsIsogeny.flat`, and the kernel
`A[n]` has order `n ^ (2 * g)` by `AlgebraicGeometry.finrankΓ_torsionSubgroupScheme`. -/
theorem finrank_npow_id (n : ℕ) (hn : 0 < n) (y : A.left) :
    (𝟙 A ^ n).left.finrank y = n ^ (2 * IsAbelianVariety.dim A) := by
  have := isIsogeny_npow_id (A := A) n hn
  rw [IsIsogeny.finrank_eq, isogenyDegree_npow_id n hn]

/-- Blueprint `proposition-multiplication-n--1`: Multiplication by `n` is finite flat of degree
`n ^ (2 * g)`.

Multiplication by `0 < n` on an abelian variety of dimension `g` is finite locally free of
degree `n ^ (2 * g)`: it is an isogeny of that degree (`AlgebraicGeometry.isogenyDegree_npow_id`),
hence `AlgebraicGeometry.IsIsogeny.isFiniteLocallyFreeOfDegree` applies. -/
theorem isFiniteLocallyFreeOfDegree_npow_id (n : ℕ) (hn : 0 < n) :
    (𝟙 A ^ n).left.IsFiniteLocallyFreeOfDegree (n ^ (2 * IsAbelianVariety.dim A)) := by
  have := isIsogeny_npow_id (A := A) n hn
  exact isogenyDegree_npow_id (A := A) n hn ▸ IsIsogeny.isFiniteLocallyFreeOfDegree (𝟙 A ^ n)

/-- Blueprint `proposition-multiplication-n--1`, part (b): Basic facts about isogenies.

Multiplication by `0 < n` on an abelian variety is an fppf covering: it is flat, locally of
finite presentation (`AlgebraicGeometry.isFiniteLocallyFreeOfDegree_npow_id`) and surjective
(`AlgebraicGeometry.surjective_npow_id`). -/
theorem singleton_mem_fppfPrecoverage_npow_id (n : ℕ) (hn : 0 < n) :
    Presieve.singleton (𝟙 A ^ n).left ∈ Scheme.fppfPrecoverage A.left := by
  have := isFiniteLocallyFreeOfDegree_npow_id (A := A) n hn
  have := surjective_npow_id A n hn
  exact Scheme.Hom.singleton_mem_fppfPrecoverage _

/-- Blueprint `corollary-torsion-jacobian-field-extension--3`: Surjectivity of multiplication by `n`
on points.

Let `A` be an abelian variety over an algebraically closed field `K` and `0 < n`. Then
`[n] : A(K) ⟶ A(K)` is surjective: `A(K)` is a divisible abelian group.

This is also blueprint `corollary-torsion-jacobian-field-extension--3`. As `[n]` is finite and
surjective, every `K`-point of `A` lifts along it
(`AlgebraicGeometry.exists_comp_eq_of_isFinite_of_surjective`, blueprint
`corollary-torsion-jacobian-field-extension--3`). -/
theorem surjective_npow_points [IsAlgClosed K] (n : ℕ) (hn : 0 < n) :
    Function.Surjective fun a : 𝟙_ (Over (Spec (.of K))) ⟶ A ↦ a ^ n := by
  have := isIsogeny_npow_id (A := A) n hn
  have := IsIsogeny.isFinite (𝟙 A ^ n)
  intro b
  obtain ⟨x, hx⟩ := exists_comp_eq_of_isFinite_of_surjective (𝟙 A ^ n).left b.left
  refine ⟨Over.homMk (U := 𝟙_ _) (V := A) x ?_, ?_⟩
  · rw [← Over.w (𝟙 A ^ n), reassoc_of% hx, Over.w b]
  · dsimp only
    rw [← Category.comp_id (Over.homMk _ _), ← comp_pow]
    exact Over.OverMorphism.ext hx

end AlgebraicGeometry
