# Sections of central extensions by diagonalizable groups: Hopf algebras

Worker 3502 wrote this module for Task 7804 (Milne, *Algebraic Groups* (2017),
Proposition 16.28). It generalizes the first half of
[`CentralDiagonalizableExtensionHopf`](CentralDiagonalizableExtensionHopf.md)
(Worker 603) from the quotient Hopf algebra `K[ℤ^I]` of a split torus to an
arbitrary commutative Hopf algebra `B`. It then uses the result to construct a
section, which that module does not do.

Throughout, `K` is a field, `A` and `B` are commutative Hopf algebras over `K`,
`N` is a commutative group, and `φ : B →ₐc[K] A` and
`π : A →ₐc[K] K[N]` are bialgebra maps. Geometrically `Spec A = E` is a group,
`Spec π : D(N) → E` is a central closed subgroup and `Spec φ : E → Spec B` is
the quotient map, so that `Spec B = E / D(N)`. The grading of `A` defined by `π`
(`GroupAlgebraCoaction.grade π n`) is the decomposition of `A` under the
translation action of `D(N)`.

## Contents

All declarations are in the namespace `Langlands.CentralExtensionSectionHopf`.

* `IsCentralExtension φ π`: the structure of
  `CentralDiagonalizableExtensionHopf.IsCentralExtension`, with `K[ℤ^I]`
  replaced by `B`. Its five fields say that `φ` is injective, `π` is surjective,
  `π ∘ φ` is trivial (`π (φ b) = ε(b) · 1`), `π` is central
  (`GroupAlgebraCoaction.IsCentral`), and every element of degree `0` lies in the
  image of `φ`.
* `map_mem_grade_zero`, `exists_unit_mem_grade`, `divide`, `map_divide`,
  `map_divide_mul`, `map_proj_proj`, `comul_eq_map_mul`, `map_map_injective`:
  copied from `CentralDiagonalizableExtensionHopf` with `K[ℤ^I]` replaced by `B`.
  Their proofs never used the special form of `K[ℤ^I]` except in one place:
  `exists_unit_mem_grade` now assumes `[Subsingleton (CommRing.Pic B)]` instead of
  using `IntLatticeAlgebra.subsingleton_pic`. Each homogeneous component
  `grade π n` is an invertible `B`-submodule of `A` (its product with
  `grade π (-n)` is `B`), so with trivial Picard group it is spanned by a unit
  `u` of `A`. For such a unit, `comul u = (φ ⊗ φ) f · (u ⊗ u)` for some `f`.
* `nontrivial_of_bialgebra`: a bialgebra over a field is a nontrivial ring
  (the counit sends `1` to `1`).
* `exists_isGroupLikeElem_smul`: assume
  `hB : ∀ f : B ⊗[K] B, IsUnit f → ∃ c : K, f = algebraMap K _ c` (every unit of
  `B ⊗ B` is a scalar). Then a unit `u` of degree `n` has a scalar multiple
  `c • u` that is group-like. The element `f` above is a unit with inverse `f'`
  (from `u⁻¹`), so `f = c`, `comul u = c • (u ⊗ u)`; the counit identity gives
  `c · ε(u) = 1`, and then `c • u` is group-like. This replaces the monomial
  argument of the template.
* `isGroupLikeElem_of_map`: if `φ b` is group-like, so is `b`.
* `exists_eq_algebraMap_of_isUnit`: under `hB`, every unit of `B` is a scalar
  (apply `hB` to `b ⊗ 1` and multiply out with `Algebra.TensorProduct.lmul'`).
* `eq_one_of_isGroupLikeElem_mem_grade_zero`: under `hB`, the only group-like
  element of degree `0` is `1`. Such an element is `φ b` with `b` group-like,
  hence a unit, hence a scalar `c` with `c = ε(b) = 1`.
* `degree_injective`, `exists_degree_eq`, `degreeEquiv`: the published degree
  map `CentralDiagonalizableExtensionHopf.degree π :
  Additive (GroupLike K A) →+ N` (`π g = Xⁿ` for a group-like `g` of degree `n`)
  is injective by the previous item and surjective by `exists_unit_mem_grade`
  and `exists_isGroupLikeElem_smul`; `degreeEquiv` is the resulting additive
  equivalence. So every component contains exactly one group-like element.
* `groupLikeOf n`: the group-like element of degree `n`, with
  `groupLikeOf_isGroupLikeElem`, `groupLikeOf_mem_grade`, `groupLikeOf_add`
  (`g_{m+n} = g_m g_n`) and `groupLikeOf_zero` (`g_0 = 1`).
* `sectionCharacter`: the monoid map `Multiplicative N →* A`, `n ↦ g_{-n}`.
* `sectionAux : A →ₐ[K] A`: the composite of the coaction
  `GroupAlgebraCoaction.coaction π : A →ₐ[K] A[N]` with the `A`-algebra map
  `AddMonoidAlgebra.lift A A N sectionCharacter`. Thus
  `sectionAux a = ∑ₙ aₙ g_{-n}`, where `aₙ = proj π n a`
  (`sectionAux_of_mem`, `sectionAux_proj`). Its values have degree `0`
  (`sectionAux_mem_grade_zero`). It preserves the counit (`counit_sectionAux`)
  and the comultiplication (`comul_sectionAux`): for `a` of degree `n`, centrality
  gives `comul a ∈ A_n ⊗ A_n` (`IsCentral.comul_of_mem`), so both sides equal
  `comul a · (g_{-n} ⊗ g_{-n})`. `eq_of_forall_proj` reduces both identities to
  homogeneous elements through `GroupAlgebraCoaction.sum_proj`.
* `sectionAlgHom : A →ₐ[K] B`: `sectionAux` followed by the inverse of `φ` on its
  range (`AlgEquiv.ofInjective`); `map_sectionAlgHom` says
  `φ (sectionAlgHom a) = sectionAux a`.
* `sectionBialgHom : A →ₐc[K] B`: `sectionAlgHom` as a bialgebra map
  (`BialgHom.ofAlgHom`); the counit and comultiplication identities are checked
  after applying the injective maps `φ` and `φ ⊗ φ`. `sectionBialgHom_map` says
  `sectionBialgHom (φ b) = b`, since `φ b` has degree `0` and `g_0 = 1`.
* `exists_section`: with trivial Picard group of `B` and `hB`, there is a
  bialgebra map `σ : A →ₐc[K] B` with `σ (φ b) = b` for all `b`.
* `subsingleton_pic_of_algEquiv`: a `K`-algebra isomorphic to a polynomial ring
  `MvPolynomial ι K` has trivial Picard group. Mathlib's instance for domains
  with a gcd (polynomial rings over a field are unique factorization domains) is
  transported along the isomorphism with `CommRing.Pic.mapRingHom`.
* `exists_eq_algebraMap_of_isUnit_tensor`: if `B ≃ₐ[K] MvPolynomial ι K`, then
  `B ⊗ B ≃ₐ[K] MvPolynomial (ι ⊕ ι) K` (`Algebra.TensorProduct.congr` and
  `MvPolynomial.tensorEquivSum`), whose units are constants
  (`MvPolynomial.isUnit_iff_eq_C_of_isReduced`).
* `exists_section_of_algEquiv`: if `B ≃ₐ[K] MvPolynomial ι K` and
  `IsCentralExtension φ π`, there is a bialgebra map `σ : A →ₐc[K] B` with
  `σ ∘ φ = id`.

## Geometric meaning and provenance

The section `σ` is a homomorphic section `E / D(N) → E` of the quotient map.
The group-like element `g_n` of degree `n` is a character of `E` extending the
character `n` of `D(N)`, and `a ↦ ∑ₙ aₙ g_{-n}` is the coordinate map of
`x ↦ x · r(x)⁻¹`, where `r : E → D(N)` is the retraction defined by these
characters.

This is an internal derived argument, not a transcription of a source proof.
Milne's proof of Proposition 16.28 (p.334) uses induction on `dim U` and
Proposition 15.25, whose proof (p.315) uses that `Pic(𝔸¹) = 0` and that the
extension is then a Hochschild extension. The argument here uses instead that
the Picard group of the polynomial ring `O(U)` is trivial and that the units of
`O(U × U)` are constants, for all `dim U` at once. The copied declarations
follow [`CentralDiagonalizableExtensionHopf`](CentralDiagonalizableExtensionHopf.md);
its Markdown explains their proofs.
