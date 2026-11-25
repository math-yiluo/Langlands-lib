/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.AlgebraicGeometry.Group.Abelian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Mon

/-!
# Torsion subgroup schemes and isogenies

Following Mathlib, a group scheme over a field `K` (blueprint `def-sc-group-scheme`) is an object
`G` of `Over (Spec (.of K))` equipped with `CategoryTheory.GrpObj G`; it is commutative if
`CategoryTheory.IsCommMonObj G`, a homomorphism is a morphism `f` with `CategoryTheory.IsMonHom f`,
and the kernel of `f` is `CategoryTheory.GrpObj.ker f`. The group scheme `G` is finite if
`AlgebraicGeometry.IsFinite G.hom`, its order is then `AlgebraicGeometry.Scheme.Hom.finrankΓ G.hom`,
and it is étale if `AlgebraicGeometry.Etale G.hom`. Multiplication by `n` is the `n`-th power
`𝟙 G ^ n` of the identity in the group `G ⟶ G` of `CategoryTheory.GrpObj.Hom.group`. This file
introduces subgroup schemes, the `n`-torsion subgroup scheme and isogenies.

## Main definitions

- `AlgebraicGeometry.IsSubgroupScheme`, `AlgebraicGeometry.IsNormalSubgroupScheme`,
  `AlgebraicGeometry.IsClosedSubgroupScheme`: (normal, closed) subgroup schemes.
- `AlgebraicGeometry.torsionSubgroupScheme`: the `n`-torsion subgroup scheme `G[n]`.
  Being a kernel, it is itself a group scheme (`CategoryTheory.GrpObj.instGrpObjKer`).
- `AlgebraicGeometry.torsionByEquiv`: the `K`-points of `G[n]` are the `n`-torsion of `G(K)`.
- `AlgebraicGeometry.torsionByPointsEquiv`: the same for `T`-points, `T` any `K`-scheme.
- `AlgebraicGeometry.torsionSubgroupSchemeMul`: multiplication by `k` from `G[k * n]` to `G[n]`.
- `AlgebraicGeometry.IsIsogeny`: a surjective homomorphism of group schemes with finite kernel.
- `AlgebraicGeometry.isogenyDegree`: the degree of an isogeny, the order of its kernel.

## Main statements

- `AlgebraicGeometry.isMonHom_npow_id`: the `n`-fold sum on a commutative group scheme is a
  homomorphism.
- `AlgebraicGeometry.isClosedSubgroupScheme_kerι`: the kernel of a homomorphism of group
  schemes is a closed subgroup scheme, and it is normal (`isNormalSubgroupScheme_kerι`).
- `AlgebraicGeometry.etale_SpecMap_algebraMap_tfae`: a finite `K`-algebra `A` is étale if and
  only if `Ω[A⁄K] = 0`, if and only if `A` is a finite product of finite separable extensions.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

variable {K : Type u} [Field K]

/-- Blueprint `definition-abelian-variety`: The `n`-fold sum is a homomorphism.

Let `G` be a commutative group scheme over `K`. Then the `n`-fold sum map `[n] : G ⟶ G` is a
homomorphism of group schemes: it is the `n`-th power of the homomorphism `𝟙 G` in the
commutative monoid `G ⟶ G`, and such powers are homomorphisms
(`CategoryTheory.MonObj.isMonHom_pow`, blueprint `definition-abelian-variety`). -/
instance isMonHom_npow_id (G : Over (Spec (.of K))) [GrpObj G] [IsCommMonObj G] (n : ℕ) :
    IsMonHom (𝟙 G ^ n) :=
  MonObj.isMonHom_pow _ n

section SubgroupScheme

variable {Z G : Over (Spec (.of K))} [GrpObj Z] [GrpObj G]

/-- Blueprint `def-sc-group-scheme-subgroup`: Subgroup schemes.

A homomorphism `i : Z ⟶ G` of group schemes over `K` exhibits `Z` as a *subgroup scheme* of `G`
if for every `K`-algebra `R` the induced map `Z(R) ⟶ G(R)` on `R`-points is injective; an
`R`-point of `Z` is a morphism `Spec R ⟶ Z` over `Spec K`. -/
class IsSubgroupScheme (i : Z ⟶ G) : Prop extends IsMonHom i where
  injective_comp (R : Type u) [CommRing R] [Algebra K R] :
    Function.Injective fun x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K R))) ⟶ Z ↦
      x ≫ i

/-- Blueprint `def-sc-group-scheme-subgroup`: Normal subgroup schemes.

A subgroup scheme `i : Z ⟶ G` is *normal* if for every `K`-algebra `R` the image of
`Z(R) ⟶ G(R)` is a normal subgroup of `G(R)`. -/
class IsNormalSubgroupScheme (i : Z ⟶ G) : Prop extends IsSubgroupScheme i where
  normal_range (R : Type u) [CommRing R] [Algebra K R] :
    (IsMonHom.monoidHom i (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K R))))).range.Normal

/-- Blueprint `def-sc-group-scheme-subgroup`: Closed subgroup schemes.

A subgroup scheme `i : Z ⟶ G` is *closed* if `i` is a closed immersion. Equivalently, `Z` is a
closed subscheme of `G` whose `R`-points form a subgroup of `G(R)` for every `K`-algebra `R`,
the group structure on `Z` being the one through which the operations of `G` factor
(`CategoryTheory.GrpObj.ofMono`). -/
class IsClosedSubgroupScheme (i : Z ⟶ G) : Prop extends IsSubgroupScheme i where
  isClosedImmersion : IsClosedImmersion i.left

attribute [instance] IsClosedSubgroupScheme.isClosedImmersion

/-- A homomorphism of group schemes which is a monomorphism is a subgroup scheme. -/
theorem IsSubgroupScheme.of_mono (i : Z ⟶ G) [IsMonHom i] [Mono i] : IsSubgroupScheme i where
  injective_comp _ _ _ _ _ h := (cancel_mono i).1 h

end SubgroupScheme

section Kernel

variable {A B : Over (Spec (.of K))} [GrpObj B]

/-- Blueprint `definition-abelian-variety--3`: the kernel `ker f ⟶ A` of a morphism `f : A ⟶ B` to a
group scheme over `K` is a closed immersion.

The unit section `Spec K ⟶ B` is a closed immersion, being a section of `B ⟶ Spec K` with
target a point (no separatedness is needed), and `ker f ⟶ A` is its base change along `f`. -/
theorem isClosedImmersion_kerι (f : A ⟶ B) : IsClosedImmersion (GrpObj.kerι f).left :=
  MorphismProperty.of_isPullback ((GrpObj.isPullback_kerι f).map (Over.forget _)).flip
    (inferInstanceAs (IsClosedImmersion η[B].left))

variable [GrpObj A] (f : A ⟶ B) [IsMonHom f]

/-- Blueprint `definition-abelian-variety--3`: Kernels are normal subgroup schemes.

For a homomorphism `f : A ⟶ B` of group schemes over `K`, the kernel `ker f` is a group scheme
(`CategoryTheory.GrpObj.instGrpObjKer`) whose `R`-points are the kernel of `f(R)`
(`CategoryTheory.GrpObj.kerRepresentableBy`, `CategoryTheory.GrpObj.range_monoidHom_kerι`), and
`kerι f : ker f ⟶ A` is a normal subgroup scheme. -/
instance isNormalSubgroupScheme_kerι : IsNormalSubgroupScheme (GrpObj.kerι f) where
  toIsSubgroupScheme := .of_mono _
  normal_range _ _ _ := by
    rw [GrpObj.range_monoidHom_kerι]
    infer_instance

/-- Blueprint `definition-abelian-variety--3` (and `def-sc-group-scheme`): Kernels are closed
subgroup schemes.

For a homomorphism `f : A ⟶ B` of group schemes over `K`, `kerι f : ker f ⟶ A` is a closed
subgroup scheme (`AlgebraicGeometry.isClosedImmersion_kerι`). -/
instance isClosedSubgroupScheme_kerι : IsClosedSubgroupScheme (GrpObj.kerι f) where
  isClosedImmersion := isClosedImmersion_kerι f

end Kernel

section Etale

/-- Blueprint `proposition-multiplication-n--2`: Finite étale algebras.

For a finite algebra `A` over a field `K`, the following are equivalent: `Spec A ⟶ Spec K` is
étale; `Ω[A⁄K] = 0`; `A` is a *finite étale `K`-algebra*, a finite product of finite separable
field extensions of `K`. -/
theorem etale_SpecMap_algebraMap_tfae (A : Type u) [CommRing A] [Algebra K A]
    [Module.Finite K A] :
    List.TFAE [Etale (Spec.map (CommRingCat.ofHom (algebraMap K A))), Subsingleton Ω[A⁄K],
      ∃ (I : Type u) (_ : Finite I) (L : I → Type u) (_ : ∀ i, Field (L i))
        (_ : ∀ i, Algebra K (L i)) (_ : A ≃ₐ[K] Π i, L i),
        ∀ i, Module.Finite K (L i) ∧ Algebra.IsSeparable K (L i)] := by
  have h : Etale (Spec.map (CommRingCat.ofHom (algebraMap K A))) ↔ Algebra.Etale K A := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale), CommRingCat.hom_ofHom,
      RingHom.etale_algebraMap]
  tfae_have 1 ↔ 2 := h.trans Algebra.Etale.iff_subsingleton_kaehlerDifferential_of_field
  tfae_have 1 ↔ 3 := h.trans (Algebra.Etale.iff_exists_algEquiv_prod K A)
  tfae_finish

/-- Blueprint `proposition-multiplication-n--2`: a finite scheme `X` over a field `K`, for
instance a finite group scheme, is étale over `K` if and only if `Γ(X, 𝒪_X)` is a finite étale
`K`-algebra (`Algebra.Etale.iff_exists_algEquiv_prod`). -/
theorem Scheme.Hom.etale_iff_etale_ΓAlgebra_of_isFinite {X : Scheme.{u}}
    (h : X ⟶ Spec (.of K)) [IsFinite h] :
    Etale h ↔
      letI := h.ΓAlgebra
      Algebra.Etale K Γ(X, ⊤) := by
  have := isAffine_of_isAffineHom h
  exact h.etale_iff_etale_ΓAlgebra

end Etale

/-- Blueprint `definition-abelian-variety--3`: Multiplication by `n` and `n`-torsion.

This is also blueprint `definition-abelian-variety--3`.

The `n`-torsion subgroup scheme `G[n]` of a group scheme `G` over `K` is the kernel of the
`n`-th power map `𝟙 G ^ n`, which on points is `a ↦ a + ⋯ + a`:

```
  G[n] ──────────────▶ 𝟙_ (Over (Spec (.of K)))
    │                            │
    │                            │ η[G]
    ▼                            ▼
    G ───── 𝟙 G ^ n ───────────▶ G
```
-/
noncomputable def torsionSubgroupScheme (G : Over (Spec (.of K))) [GrpObj G] (n : ℕ) :
    Over (Spec (.of K)) :=
  GrpObj.ker (𝟙 G ^ n)

/-- The `n`-torsion of a commutative group scheme is itself a group scheme, being a kernel. -/
noncomputable instance (G : Over (Spec (.of K))) [GrpObj G] [IsCommMonObj G] (n : ℕ) :
    GrpObj (torsionSubgroupScheme G n) :=
  inferInstanceAs (GrpObj (GrpObj.ker (𝟙 G ^ n)))

/-- The inclusion `G[n] ⟶ G` of the `n`-torsion subgroup scheme, that is,
`CategoryTheory.GrpObj.kerι (𝟙 G ^ n)`. -/
noncomputable def torsionSubgroupScheme.ι (G : Over (Spec (.of K))) [GrpObj G] (n : ℕ) :
    torsionSubgroupScheme G n ⟶ G :=
  GrpObj.kerι (𝟙 G ^ n)

instance (G : Over (Spec (.of K))) [GrpObj G] (n : ℕ) : Mono (torsionSubgroupScheme.ι G n) :=
  GrpObj.mono_kerι _

/-- The inclusion `G[n] ⟶ G` is killed by `[n]`. -/
theorem torsionSubgroupScheme.ι_pow (G : Over (Spec (.of K))) [GrpObj G] (n : ℕ) :
    torsionSubgroupScheme.ι G n ^ n = 1 := by
  have h := GrpObj.kerι_comp (𝟙 G ^ n)
  simp only [comp_pow, Category.comp_id] at h
  exact h

/-- Blueprint `definition-abelian-variety--3`: the `n`-torsion subgroup scheme `G[n]` of a
commutative group scheme is a closed subgroup scheme of `G`, being the kernel of the homomorphism
`[n] = 𝟙 G ^ n` (`AlgebraicGeometry.isMonHom_npow_id`,
`AlgebraicGeometry.isClosedSubgroupScheme_kerι`). -/
instance isClosedSubgroupScheme_torsionSubgroupScheme_ι (G : Over (Spec (.of K))) [GrpObj G]
    [IsCommMonObj G] (n : ℕ) : IsClosedSubgroupScheme (torsionSubgroupScheme.ι G n) :=
  isClosedSubgroupScheme_kerι _

/-- Blueprint `definition-abelian-variety--3`: the `T`-points of the `n`-torsion subgroup scheme.

For a commutative group scheme `G` over `K` and a `K`-scheme `T`, the `T`-points of `G[n]` are
the `n`-torsion of the group `G(T)`, written additively: the `n`-torsion point `x` corresponds to
the unique point of `G[n]` whose image under `AlgebraicGeometry.torsionSubgroupScheme.ι` is `x`.
For `T = Spec K` this is `AlgebraicGeometry.torsionByEquiv`. -/
noncomputable def torsionByPointsEquiv (G : Over (Spec (.of K))) [GrpObj G] [IsCommMonObj G]
    (n : ℕ) (T : Over (Spec (.of K))) :
    AddSubgroup.torsionBy (Additive (T ⟶ G)) (n : ℤ) ≃ (T ⟶ torsionSubgroupScheme G n) :=
  (Equiv.subtypeEquiv (p := fun x ↦ x ∈ AddSubgroup.torsionBy _ (n : ℤ))
    (q := fun x ↦ x ∈ MonoidHom.ker (IsMonHom.monoidHom (𝟙 G ^ n) T)) Additive.toMul
    fun x ↦ by
      rw [MonoidHom.mem_ker, AddSubgroup.torsionBy, Submodule.mem_toAddSubgroup,
        Submodule.mem_torsionBy_iff, natCast_zsmul]
      change n • x = 0 ↔ x.toMul ≫ 𝟙 G ^ n = 1
      rw [comp_pow, Category.comp_id]
      rfl).trans (GrpObj.kerRepresentableBy (𝟙 G ^ n)).homEquiv.symm

/-- The `K`-points of the `n`-torsion subgroup scheme `G[n]` of a commutative group scheme `G`
are the `n`-torsion points of `G`: the `n`-torsion of the group `G(K)`, written additively, is
in bijection with `𝟙_ (Over (Spec (.of K))) ⟶ G[n]`, a point `x` of `G[n]` corresponding to
its image `x ≫ GrpObj.kerι (𝟙 G ^ n)` in `G(K)`. This is the case `T = Spec K` of
`AlgebraicGeometry.torsionByPointsEquiv`. -/
noncomputable def torsionByEquiv (G : Over (Spec (.of K))) [GrpObj G] [IsCommMonObj G] (n : ℕ) :
    AddSubgroup.torsionBy (Additive (𝟙_ (Over (Spec (.of K))) ⟶ G)) (n : ℤ) ≃
      (𝟙_ (Over (Spec (.of K))) ⟶ torsionSubgroupScheme G n) :=
  torsionByPointsEquiv G n (𝟙_ _)

@[simp]
theorem torsionByPointsEquiv_comp_ι (G : Over (Spec (.of K))) [GrpObj G] [IsCommMonObj G]
    (n : ℕ) (T : Over (Spec (.of K))) (x : AddSubgroup.torsionBy (Additive (T ⟶ G)) (n : ℤ)) :
    torsionByPointsEquiv G n T x ≫ torsionSubgroupScheme.ι G n =
      (x : Additive (T ⟶ G)).toMul :=
  GrpObj.kerLift_kerι _ _ _

/-- Blueprint `definition-abelian-variety--3`: multiplication by `k` maps `G[m]` to `G[n]` when
`m = k * n`.

This is the morphism `G[m] ⟶ G[n]` through which `G[m] ⟶ G ⟶ G`, the inclusion followed by
`[k] = 𝟙 G ^ k`, factors; for `G` an abelian variety, `m = ℓ ^ (n + 1)`, `n = ℓ ^ n` and `k = ℓ`
these are the transition maps of the inverse system defining the Tate module (blueprint
`definition-tate-module`). -/
noncomputable def torsionSubgroupSchemeMul (G : Over (Spec (.of K))) [GrpObj G] {m n : ℕ}
    (k : ℕ) (h : m = k * n) : torsionSubgroupScheme G m ⟶ torsionSubgroupScheme G n :=
  GrpObj.kerLift (𝟙 G ^ n) (torsionSubgroupScheme.ι G m ^ k) <| by
    rw [comp_pow, Category.comp_id, ← pow_mul, ← h, torsionSubgroupScheme.ι_pow]
    rfl

@[reassoc (attr := simp)]
theorem torsionSubgroupSchemeMul_ι (G : Over (Spec (.of K))) [GrpObj G] {m n : ℕ}
    (k : ℕ) (h : m = k * n) :
    torsionSubgroupSchemeMul G k h ≫ torsionSubgroupScheme.ι G n =
      torsionSubgroupScheme.ι G m ^ k :=
  GrpObj.kerLift_kerι _ _ _

/-- Blueprint `proposition-multiplication-n--1`: Isogenies and their degree.

This is also blueprint `proposition-multiplication-n--1`.

An *isogeny* `f : A ⟶ B` of group schemes over `K` is a surjective homomorphism with finite
kernel. The blueprint defines isogenies between abelian varieties; the definition makes sense
for arbitrary group schemes, but it is only for abelian varieties that
`AlgebraicGeometry.isogenyDegree` is the degree of `f` as a finite flat morphism (see
`AlgebraicGeometry.IsIsogeny.finrank_eq`). -/
class IsIsogeny {A B : Over (Spec (.of K))} [GrpObj A] [GrpObj B] (f : A ⟶ B) : Prop
    extends IsMonHom f, Surjective f.left where
  /-- The kernel of an isogeny is a finite group scheme. -/
  isFinite_ker : IsFinite (GrpObj.ker f).hom

attribute [instance] IsIsogeny.isFinite_ker

/-- Blueprint `proposition-multiplication-n--1`: the degree of an isogeny
`f : A ⟶ B`, the order of its kernel.

This is only the degree of `f` as a finite flat morphism when `f` is an isogeny of abelian
varieties; outside that range it is the order of the kernel and nothing more. -/
noncomputable def isogenyDegree {A B : Over (Spec (.of K))} [GrpObj A] [GrpObj B] (f : A ⟶ B) :
    ℕ :=
  (GrpObj.ker f).hom.finrankΓ

end AlgebraicGeometry
