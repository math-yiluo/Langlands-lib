# Quotient data of abelian schemes by finite étale subgroup schemes

This module gives a generic interface for the quotient of an actual abelian scheme by a finite étale closed subgroup scheme. It specifies the data only. It does not construct a quotient, and no existence of quotients is assumed or proved. The base `S : Scheme.{u}` is an arbitrary scheme in an arbitrary universe; the consumer's universe-zero case is the instance `u := 0`. No noetherian, connectedness, projectivity or characteristic hypothesis appears.

All declarations are in the namespace `Langlands.AbelianScheme`. The module reuses the published interfaces `Langlands.AbelianScheme` (module `Basic`), `Langlands.CommGroupScheme` (module `GroupScheme`), `Langlands.GroupScheme.kernel` (module `Kernel`) and `Langlands.AbelianScheme.IsIsogeny` (module `IsogenySpecialization`). The scheme predicates `IsClosedImmersion`, `IsFinite`, `Etale`, `Surjective` and `Flat` are Mathlib's. No imported Lean/Markdown pair is changed.

## Finite étale closed subgroups

`FiniteEtaleSubgroup A`, for `A : AbelianScheme S`, is a structure with the following fields.

- `G : CommGroupScheme S` is the subgroup scheme itself, an actual commutative group object in `Over S`. The whole scheme `G.X.left` is kept, including any nilpotent structure. It is not replaced by a set of geometric points or by a finite abstract group.
- `inclusion : G ⟶ A.toCommGroupScheme` is an actual homomorphism of commutative group schemes over `S`.
- `isClosedImmersion` states `IsClosedImmersion (CommGroupScheme.hom inclusion)`. Here `CommGroupScheme.hom inclusion : G.X.left ⟶ A.X.left` is the underlying morphism of schemes.
- `isFinite` and `etale` state `IsFinite G.X.hom` and `Etale G.X.hom`, where `G.X.hom : G.X.left ⟶ S` is the structure morphism of the subgroup scheme.

The three conditions are declared as instances, so they are available by type-class inference for any `K : FiniteEtaleSubgroup A`. A closed immersion is a monomorphism of schemes, so `inclusion` identifies `G` with a closed subscheme of `A` stable under the group law. The structure keeps `G` and its inclusion as data, rather than a subscheme determined by an ideal sheaf. Subgroups that differ by an isomorphism compatible with the inclusions are not identified by the interface.

## Quotient data

`FiniteEtaleSubgroup.QuotientData K`, for `K : FiniteEtaleSubgroup A`, is a structure with the following fields. The selected entry declaration of this unit is `Langlands.AbelianScheme.FiniteEtaleSubgroup.QuotientData`.

- `B : AbelianScheme S` is the quotient, an actual abelian scheme over the same base. By the published definition it is a commutative group scheme whose structure morphism is smooth and proper with geometrically connected fibres.
- `q : A ⟶ B` is an actual homomorphism of abelian schemes.
- `isFinite`, `etale` and `surjective` state that the underlying scheme morphism `AbelianScheme.hom q : A.X.left ⟶ B.X.left` is finite, étale and surjective. They are declared as instances.
- `isPullback` states

  ```text
  IsPullback (CommGroupScheme.hom K.inclusion) K.G.X.hom
    (AbelianScheme.hom q) η[B.X].left
  ```

  This is the square of actual scheme morphisms with vertices `K.G.X.left`, `A.X.left`, `S` and `B.X.left`. Its right side `η[B.X].left : S ⟶ B.X.left` is the unit section of `B`. The condition says that `K.G.X.left`, with the inclusion and its structure morphism, is a fibre product of `q` and the unit section of `B`. So `K` is exactly the scheme kernel of `q`, in the sense of Definition (3.13) of the source below, with its full scheme structure.

The task allowed this condition to be encoded either as the cartesian square or as an isomorphism with `GroupScheme.kernel (groupHom q)`. The square is chosen as the field. The isomorphism is derived from it below.

## Accessors

For `D : K.QuotientData`:

- `D.isPullback` is the cartesian square itself, as a field.
- `D.flat : Flat (AbelianScheme.hom D.q)` follows from Mathlib's instances: étale morphisms are smooth, and smooth morphisms are flat.
- `D.isIsogeny : IsIsogeny D.q` assembles `isFinite`, `flat` and `surjective` into the published finite-flat-surjective predicate `Langlands.AbelianScheme.IsIsogeny`.
- `D.kernelSchemeIso : K.G.X.left ≅ (GroupScheme.kernel (groupHom D.q)).X.left` is the comparison of two pullbacks of the same cospan. One is `D.isPullback`; the other is the published `GroupScheme.kernel_isPullback_scheme`. It is Mathlib's `IsPullback.isoIsPullback`. The lemmas `kernelSchemeIso_hom_inclusion` and `kernelSchemeIso_hom_structure` state that it is compatible with the maps to `A.X.left` and to `S`.
- `D.kernelOverIso : K.G.X ≅ (GroupScheme.kernel (groupHom D.q)).X` is the same isomorphism in `Over S`, and `kernelOverIso_hom_inclusion` states its compatibility with the inclusions in `Over S`.
- `D.kernelIso : K.G.toGrp ≅ GroupScheme.kernel (groupHom D.q)` is an isomorphism of group schemes. It is built with Mathlib's `Grp.mkIso` from `kernelOverIso`. Compatibility with unit and multiplication is checked after composing with the kernel inclusion, which is a monomorphism by the published `GroupScheme.kernelι_mono`. Both sides then reduce to the corresponding identities for the homomorphism `K.inclusion`.
- `kernelIso_hom_inclusion` states `D.kernelIso.hom ≫ GroupScheme.kernelι (groupHom D.q) = CommGroupScheme.groupHom K.inclusion`. So the second encoding allowed by the task, an isomorphism with the published kernel that commutes with inclusion, is also available.

## Constructors from a given homomorphism

These constructors are direct consequences of supplied data. They are not existence statements for quotients.

- `FiniteEtaleSubgroup.ofKernel q`, for `q : A ⟶ B` with finite and étale underlying morphism, is the published scheme kernel `GroupScheme.kernel (groupHom q)` as a finite étale closed subgroup of `A`. Commutativity is the published instance `kernel_isCommMonObj`. The closed-immersion field is `kernelι_isClosedImmersion`, which applies because the abelian scheme `B` is proper, hence separated, over `S`. Finiteness and étaleness of the structure morphism follow by base change from `q` along the published scheme square `kernel_isPullback_scheme`, using Mathlib's `MorphismProperty.of_isPullback`.
- `FiniteEtaleSubgroup.QuotientData.ofKernel q`, if moreover `q` is surjective, is quotient data for `FiniteEtaleSubgroup.ofKernel q` with `B` and `q` themselves; its square is `kernel_isPullback_scheme`.

## Source and provenance

The source is B. Edixhoven, G. van der Geer and B. Moonen, *Abelian Varieties*, preliminary chapters, registered as `edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256 `81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`, file `literature/Edixhoven, van der Geer, Moonen - Abelian Varieties (preliminary version of the first chapters).pdf`. The cited pages were read directly. No source-specific errata note was found in the available project notes.

- Definition (3.13), printed pp. 36–37 (PDF pp. 40–41), defines the kernel of a homomorphism as the inverse image of the target unit section by a cartesian square. It notes that the kernel is closed when the target is separated. The field `isPullback` is this square.
- Theorem (4.16), printed p. 55 (PDF p. 59), constructs the quotient of a scheme by a free action of a finite locally free group scheme. Under its affineness hypothesis on orbits, the quotient map is finite locally free and `G ×_S X ≅ X ×_Y X`. Remark (4.17), printed p. 56 (PDF p. 60), notes that quasi-projectivity of `X` suffices for this hypothesis.
- (4.37), printed p. 65 (PDF p. 69), explains that if the fppf quotient `G/H` by a normal subgroup scheme is representable, then it is a group scheme, `0 → H → G → G/H → 0` is exact, and homomorphisms killing `H` factor through `G/H`. Theorem (4.39)(c), printed p. 66 (PDF p. 70), gives representability for finite locally free `H` under an affineness condition.
- Example (4.40), printed p. 66 (PDF p. 70), states that the quotient of an abelian variety over a field by a closed subgroup scheme is again an abelian variety. It concerns a field base only.

These results motivate the interface. None of them is formalized here: no quotient is constructed and no representability, exactness or universal property is asserted. The bundle is a derived specialization. It restricts the subgroup to finite étale ones, asks for an abelian-scheme quotient over an arbitrary base, and records only the properties of the quotient map and the exact kernel square, with no factorization property. Its finite, étale and surjective conditions are the properties expected of a quotient by a finite étale subgroup (finite locally free and, since the kernel is étale, étale). Existence of such data, for instance for a projective abelian scheme over a locally noetherian base, its comparison with arbitrary base change, and descent of endomorphism actions are left to separate later tasks.
