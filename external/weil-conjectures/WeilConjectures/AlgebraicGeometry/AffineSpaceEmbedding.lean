/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.AffineSpaceClosedChart
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Affine schemes over a field embed into affine space

Schemes over a field `k` are objects of `Over (Spec (.of k))`. This file provides

* the affine space `𝔸ⁿ_k = 𝔸(ULift (Fin n); Spec k)` as an object
  `AlgebraicGeometry.affineSpaceOver k n` of `Over (Spec (.of k))`, separated, quasi-compact,
  locally of finite type and smooth over `k`;
* for an open `W` of an object `S` of `Over B`, the open subscheme
  `AlgebraicGeometry.overRestrict S W` as an object of `Over B` and its open immersion
  `AlgebraicGeometry.overRestrictι S W : overRestrict S W ⟶ S`; over a field, it is separated,
  quasi-compact and of finite type whenever `S` is;
* `AlgebraicGeometry.AffineSpaceEmbedding U`: a closed immersion `i : U ⟶ 𝔸ⁿ_k` over `k`
  together with the open complement of its image, and
  `AlgebraicGeometry.affineSpaceEmbedding U`, such an embedding for every affine `U` of finite
  type over `k`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-! ### Open subschemes as objects of `Over B` -/

section OverRestrict

variable {B : Scheme.{u}} (S : Over B) (W : S.left.Opens)

/-- The open subscheme `W` of an object `S` of `Over B`, as an object of `Over B`. -/
noncomputable abbrev overRestrict : Over B :=
  Over.mk (W.ι ≫ S.hom)

/-- The open immersion `W ⟶ S` of an open subscheme, as a morphism of `Over B`. -/
noncomputable abbrev overRestrictι : overRestrict S W ⟶ S :=
  Over.homMk W.ι rfl

/-- The inclusion of an open subscheme is an open immersion. -/
instance isOpenImmersion_overRestrictι_left :
    IsOpenImmersion (overRestrictι S W).left :=
  inferInstanceAs (IsOpenImmersion W.ι)

/-- An open subscheme of a scheme locally of finite type is locally of finite type. -/
instance locallyOfFiniteType_overRestrict_hom [LocallyOfFiniteType S.hom] :
    LocallyOfFiniteType (overRestrict S W).hom :=
  inferInstanceAs (LocallyOfFiniteType (W.ι ≫ S.hom))

/-- An open subscheme of a separated scheme is separated. -/
instance isSeparated_overRestrict_hom [IsSeparated S.hom] :
    IsSeparated (overRestrict S W).hom :=
  inferInstanceAs (IsSeparated (W.ι ≫ S.hom))

/-- An open subscheme of a smooth scheme is smooth. -/
instance smooth_overRestrict_hom [Smooth S.hom] : Smooth (overRestrict S W).hom :=
  inferInstanceAs (Smooth (W.ι ≫ S.hom))

/-- The image of the open immersion of `W` is `W`. -/
lemma range_overRestrictι : Set.range (overRestrictι S W).left.base = W :=
  W.range_ι

end OverRestrict

section Field

variable {k : Type u} [Field k] (S : Over (Spec (.of k))) [LocallyOfFiniteType S.hom]
  [QuasiCompact S.hom] (W : S.left.Opens)

/-- The open immersion of an open subscheme of a quasi-compact scheme locally of finite type over a
field is quasi-compact (the scheme is noetherian). -/
instance quasiCompact_overRestrictι_left : QuasiCompact (overRestrictι S W).left := by
  have : IsLocallyNoetherian S.left := LocallyOfFiniteType.isLocallyNoetherian S.hom
  have : CompactSpace S.left := QuasiCompact.compactSpace_of_compactSpace S.hom
  have : IsNoetherian S.left := ⟨⟩
  exact inferInstanceAs (QuasiCompact W.ι)

/-- An open subscheme of a quasi-compact scheme locally of finite type over a field is
quasi-compact over the field. -/
instance quasiCompact_overRestrict_hom : QuasiCompact (overRestrict S W).hom :=
  inferInstanceAs (QuasiCompact ((overRestrictι S W).left ≫ S.hom))

end Field

/-! ### Affine space over a field -/

section AffineSpace

variable (k : Type u) [Field k]

/-- The affine space `𝔸ⁿ_k = 𝔸(ULift (Fin n); Spec k)` as an object of
`Over (Spec (.of k))`. -/
noncomputable def affineSpaceOver (n : ℕ) : Over (Spec (.of k)) :=
  Over.mk (𝔸(ULift.{u} (Fin n); Spec (.of k)) ↘ Spec (.of k))

/-- Affine space over a field is affine. -/
instance isAffine_affineSpaceOver_left (n : ℕ) :
    IsAffine (affineSpaceOver k n).left :=
  inferInstanceAs (IsAffine 𝔸(ULift.{u} (Fin n); Spec (.of k)))

/-- Affine space is of finite type over `k`. -/
instance locallyOfFiniteType_affineSpaceOver_hom (n : ℕ) :
    LocallyOfFiniteType (affineSpaceOver k n).hom :=
  inferInstanceAs (LocallyOfFiniteType (𝔸(ULift.{u} (Fin n); Spec (.of k)) ↘ Spec (.of k)))

/-- Affine space is quasi-compact over `k`. -/
instance quasiCompact_affineSpaceOver_hom (n : ℕ) :
    QuasiCompact (affineSpaceOver k n).hom :=
  inferInstanceAs (QuasiCompact (𝔸(ULift.{u} (Fin n); Spec (.of k)) ↘ Spec (.of k)))

/-- Affine space is separated over `k`. -/
instance isSeparated_affineSpaceOver_hom (n : ℕ) :
    IsSeparated (affineSpaceOver k n).hom :=
  inferInstanceAs (IsSeparated (𝔸(ULift.{u} (Fin n); Spec (.of k)) ↘ Spec (.of k)))

/-- `𝔸ⁿ_k` is smooth of relative dimension `n` over `k`. -/
instance smoothOfRelativeDimension_affineSpaceOver_hom (n : ℕ) :
    SmoothOfRelativeDimension n (affineSpaceOver k n).hom := by
  have := AffineSpace.smoothOfRelativeDimension_over (ULift.{u} (Fin n)) (Spec (.of k))
  rwa [Nat.card_ulift, Nat.card_eq_fintype_card, Fintype.card_fin] at this

/-- Affine space is smooth over `k`. -/
instance smooth_affineSpaceOver_hom (n : ℕ) : Smooth (affineSpaceOver k n).hom :=
  SmoothOfRelativeDimension.smooth n _

end AffineSpace

/-! ### Closed embeddings of affine schemes into affine space -/

section Embedding

variable {k : Type u} [Field k]

/-- A closed immersion `i : U ⟶ 𝔸ⁿ_k` over `k` of a scheme `U` over `k` into affine space.
Its open complement is `AffineSpaceEmbedding.compl`. -/
structure AffineSpaceEmbedding (U : Over (Spec (.of k))) where
  /-- The dimension of the ambient affine space. -/
  n : ℕ
  /-- The closed immersion into affine space. -/
  i : U ⟶ affineSpaceOver k n
  /-- The morphism `i` is a closed immersion. -/
  isClosedImmersion : IsClosedImmersion i.left

attribute [instance] AffineSpaceEmbedding.isClosedImmersion

namespace AffineSpaceEmbedding

variable {U : Over (Spec (.of k))} (e : AffineSpaceEmbedding U)

/-- The open complement in `𝔸ⁿ_k` of the image of an embedding into affine space. -/
noncomputable def compl : (affineSpaceOver k e.n).left.Opens :=
  ⟨(Set.range e.i.left.base)ᶜ, e.i.left.isClosedEmbedding.isClosed_range.isOpen_compl⟩

/-- The open complement of the image of an embedding into affine space, as a scheme over `k`. -/
noncomputable abbrev complOver : Over (Spec (.of k)) :=
  overRestrict (affineSpaceOver k e.n) e.compl

/-- The open immersion of the complement of the image of an embedding into affine space. -/
noncomputable abbrev complι : e.complOver ⟶ affineSpaceOver k e.n :=
  overRestrictι (affineSpaceOver k e.n) e.compl

/-- The image of the complement is the complement of the image. -/
lemma range_complι : Set.range e.complι.left.base = (Set.range e.i.left.base)ᶜ :=
  range_overRestrictι _ _

/-- The closed embedding into affine space and the open immersion of its complement have
complementary images. -/
lemma isCompl_range : IsCompl (Set.range e.i.left.base) (Set.range e.complι.left.base) := by
  rw [range_complι]
  exact isCompl_compl

end AffineSpaceEmbedding

/-- Every affine scheme locally of finite type over a field `k` admits a closed immersion into some
affine space `𝔸ⁿ_k` over `k`. -/
theorem nonempty_affineSpaceEmbedding (U : Over (Spec (.of k))) [IsAffine U.left]
    [LocallyOfFiniteType U.hom] : Nonempty (AffineSpaceEmbedding U) := by
  obtain ⟨n, c, hc, _⟩ := exists_isClosedImmersion_affineSpace_of_isAffine U.hom
  exact ⟨⟨n, Over.homMk c hc, ‹_›⟩⟩

/-- A chosen closed immersion of an affine scheme of finite type over `k` into some affine space
`𝔸ⁿ_k` over `k`. -/
noncomputable def affineSpaceEmbedding (U : Over (Spec (.of k))) [IsAffine U.left]
    [LocallyOfFiniteType U.hom] : AffineSpaceEmbedding U :=
  Classical.choice (nonempty_affineSpaceEmbedding U)

end Embedding

end AlgebraicGeometry
