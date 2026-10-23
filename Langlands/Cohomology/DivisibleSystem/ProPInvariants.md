# Pro-`p` invariants of `ℓ`-divisible systems

Author: Worker 61. Built on `Langlands.Cohomology.DivisibleSystem.TotalComparison`
and, through it, on the InvariantTotal, Invariants and Sections modules and the
earlier modules of the series. It also uses Worker 3's
`Langlands.Cohomology.ProPInvariants.Statement` (the proposition
`ProPInvariantsExactStatement`), the Library's `isSmooth_comp`
(`Langlands.Representation.Smooth.Transfer.PullbackProof`) and the Library's
instances for `SmoothRep.toRep` (`Langlands.Representation.Category.Abelian`).
New names are in the namespace `Langlands.Cohomology` (the first section) and
`Langlands.Cohomology.DivisibleSystem` (the systems).

On p.305 Harris takes "an open normal pro-`p` subgroup `H ⊂ S(ẽ)`" acting
trivially on the cohomology and writes: "Since `p` is prime to `ℓ`, the functor
`H⁰(H, •)` is exact on `ℓ`-primary torsion modules". The Invariants module
applies the `H`-invariants degreewise to an `ℓ`-divisible system of complexes
of smooth representations only under an explicit hypothesis `hK`: every degree
of every projection stays an epimorphism on `H`-invariants. The InvariantTotal
and TotalComparison modules keep that hypothesis (as `hK`, or as `hterm`,
`hres` for the truncated smooth Godement systems).

This module derives these hypotheses for a normal pro-`p` subgroup `H` and
coefficients in which `p` is invertible, from Worker 3's proposition
`ProPInvariantsExactStatement`. That proposition is taken as a hypothesis
`hP`; it is not proved, here or (as of this module) anywhere in the Library.

## Pro-`p` subgroups and epimorphisms on invariants

`G` is a group with a topology.

- `IsProPSubgroup p H`, for `p : ℕ` and `H : Subgroup G`, is a structure in
  `Prop` with four fields: `prime : p.Prime`; `compactSpace : CompactSpace H`
  and `totallyDisconnectedSpace : TotallyDisconnectedSpace H`, for the
  subspace topology on `H`; and
  `isPGroup : ∀ N : OpenNormalSubgroup H, IsPGroup p (H ⧸ N.toSubgroup)`: the
  quotient of `H` by every open normal subgroup (open for the subspace
  topology) is a `p`-group in Mathlib's sense (every element has `p`-power
  order). These fields are exactly the hypotheses that
  `ProPInvariantsExactStatement` puts on its group, with the group taken to be
  `H`. Neither openness nor normality of `H` in `G` is a field; normality is
  the separate instance argument `[H.Normal]` wherever it is needed.
- `isSmooth_res_subtype R H A`: for a smooth representation `A` of `G`
  (`SmoothRep.{uR, uG, uV} R G`), its restriction
  `(Rep.resFunctor H.subtype).obj (SmoothRep.toRep.obj A)` to `H` is smooth
  for the subspace topology. This is `isSmooth_comp` for the continuous
  inclusion `H.subtype`: an open subgroup of `G` fixing a vector pulls back to
  an open subgroup of `H` fixing it.

From now on `G` is a topological group (`[IsTopologicalGroup G]`), so that `H`
with the subspace topology is a topological group, as
`ProPInvariantsExactStatement` requires.

- `epi_smoothQuotientInvariants_map hP hH hR f`: for
  `hP : ProPInvariantsExactStatement.{uG, uR, uV}`, `H` normal with
  `hH : IsProPSubgroup p H`, `hR : IsUnit (p : R)` and an epimorphism
  `f : A ⟶ B` of smooth representations of `G`, the morphism
  `(smoothQuotientInvariants R H).map f` of representations of `G ⧸ H` (the
  Invariants module's `H`-invariants functor) is an epimorphism.

  Proof. The fields `compactSpace` and `totallyDisconnectedSpace` of `hH` are
  made local instances. `SmoothRep.toRep` preserves epimorphisms and finite
  limits (Library instances), hence homology (Mathlib's
  `Functor.preservesHomology_of_preservesEpis_and_kernels`). The short
  complex `S = (kernel.ι f, f)` in smooth representations is short exact
  (exactness from Mathlib's `ShortComplex.exact_of_f_is_kernel` with
  `kernelIsKernel f`). Mapping it along `SmoothRep.toRep` keeps it short exact
  (`ShortComplex.ShortExact.map`), and so does restricting to `H` (Mathlib's
  `Rep.shortExact_res`). The three restricted terms are smooth by
  `isSmooth_res_subtype`. Applying `hP` at the prime `hH.prime`, the group
  `H`, the condition `hH.isPGroup`, the ring `R` and `hR` gives that the
  invariants of the restricted short complex form a short exact sequence of
  `R`-modules; in particular the invariants of the restriction of `f` are an
  epimorphism, i.e. surjective (`ModuleCat.epi_iff_surjective`). By Mathlib's
  definition of `Rep.quotientToInvariantsFunctor`, the map of invariants of
  `f` as representations of `G ⧸ H` has this same underlying function, so it
  is an epimorphism by `Rep.epi_iff_surjective`. Only the surjectivity part
  of the conclusion of `hP` is used.
- `epi_comp_smoothQuotientInvariants_map hP hH hR Φ f hf`: the same for
  `Φ ⋙ smoothQuotientInvariants R H`, where `Φ` is a functor from any
  category to smooth representations and `Φ.map f` is an epimorphism.

## A general system

`K : DivisibleSystem (CochainComplex (SmoothRep.{uR, uG, uV} R G) ℕ) ℓ`, with
`hP`, `H` normal, `hH` and `hR` as above.

- `epi_smoothQuotientInvariants_map_projection_f hP hH hR K h q`: for
  `h : m' ≤ m` and every degree `q`, the `H`-invariants of the degree-`q`
  component of the projection `K m ⟶ K m'` are an epimorphism. This is the
  hypothesis `hK` of the Invariants module. Proof: the components of the
  projections are epimorphisms (the Invariants module's `epi_projection_f`),
  and `epi_smoothQuotientInvariants_map` applies.
- `proPQuotientInvariantsComplexes hP hH hR K` and
  `proPQuotientInvariantsComplexesInclusion hP hH hR K` are the Invariants
  module's `quotientInvariantsComplexes K H hK` and
  `quotientInvariantsComplexesInclusion K H hK` (the inclusion of the inflated
  `H`-invariants into `K.toRepComplexes`) with this `hK`.

Now `H` also has finite index, `N : ℕ`, and the representations are in
`SmoothRep.{uR, uG, max w uR uG} R G` as in the InvariantTotal module, with
`hP : ProPInvariantsExactStatement.{uG, uR, max w uR uG}`.

- `proPQuotientInvariantsTotalSystem N hP hH hR K` and
  `proPQuotientInvariantsTotalSystemAugmentation N hP hH hR K` are the
  InvariantTotal module's `quotientInvariantsTotalSystem N K H hK` (Harris's
  `C_m^{•,H}` for a general system, rows `q < N`) and its totalized
  augmentation, with this `hK`.
- `proPQuotientInvariantsTotalSystemToExtend N hP hH hR K hN` is the
  TotalComparison module's `quotientInvariantsTotalSystemToExtend N K H hK hN`,
  the morphism to the `H`-invariants system extended to `ℤ`, with this `hK`;
  `hN` says that `K` vanishes in degrees `q ≥ N`.

## The truncated smooth Godement resolutions

`R`, `G`, `X`, `h`, `T : SmoothSheafDivisibleSystem R G X ℓ` and `D : ℕ` are
those of the Sections module's `smoothGodementTruncatedCompactSectionsSystem`
(all types in one universe `u`; `h` is a proof of Worker 3's unproved
proposition `SmoothGodementZeroExactStatement R G X`), `G` is a topological
group, `hP : ProPInvariantsExactStatement.{u, u, u}`, and `H`, `hH`, `hR` are
as above. The hypotheses `hterm` and `hres` are those of
`smoothGodementTruncatedCompactSectionsSystem`: the compact sections (before
taking invariants) of the projections of the term systems `F^q` (`q ≤ D`) and
of the residual system `R (D + 1)` are epimorphisms. From them and `hP`,
`epi_comp_smoothQuotientInvariants_map` gives the hypotheses of the same names
of the Invariants module, which concern the `H`-invariants of these compact
sections.

- `proPSmoothGodementTruncatedQuotientInvariantSectionsSystem h T D hP hH hR
  hterm hres` is the Invariants module's
  `smoothGodementTruncatedQuotientInvariantSectionsSystem` (Harris's system
  `{G_m(U)^H}`) with the derived hypotheses.

Now `H` also has finite index.

- `proPSmoothGodementInvariantTotalSystem h T D hP hH hR hterm hres` is the
  InvariantTotal module's `smoothGodementInvariantTotalSystem` (Harris's
  `C_m^{•,H}`, rows `q < D + 2`), and
  `proPSmoothGodementInvariantTotalSystemToExtend h T D hP hH hR hterm hres` is
  the TotalComparison module's `smoothGodementInvariantTotalSystemToExtend`,
  both with the derived hypotheses.

All these systems and morphisms are abbreviations. Since `hK` (or `hterm`,
`hres`) is a proof, they are definitionally the original constructions for
any proof of that hypothesis; they record that, given `hP`, the hypothesis
holds for pro-`p` subgroups.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), section 2, printed p.305; Worker 61 read
the page in the scanned original. Serre, *Galois Cohomology* (Springer 1997,
corrected second printing 2002), Chapter I, §1.1 (p.3), §1.3 (pp.5–6) and §1.4
(p.6); Worker 61 read them in the embedded text layer.

1. Pro-`p` subgroups. Serre §1.4 (p.6) calls a profinite group a
   pro-`p`-group "if it is a projective limit of `p`-groups, or, which amounts
   to the same thing, if its order is a power of `p`". By §1.3 the order is
   the lcm of the indices of the open normal subgroups, so this says that
   every quotient by an open normal subgroup is a finite `p`-group, which is
   the field `isPGroup` (the finiteness of these quotients follows from
   compactness and is not a field). By Serre's Proposition 0 (p.3), a compact
   totally disconnected topological group is profinite, which is what the
   fields `compactSpace` and `totallyDisconnectedSpace` say. Serre's
   compactness includes the Hausdorff property and Mathlib's `CompactSpace`
   does not; for a topological group total disconnectedness already makes
   points closed and hence the group Hausdorff, a standard fact that this
   module does not use. The fields agree with the hypotheses of Worker 3's
   `ProPInvariantsExactStatement`, so that `hP` applies to `H` with no
   conversion; Worker 3 confirmed this use of the statement.
2. The exactness of invariants. Harris's "`H⁰(H, •)` is exact on `ℓ`-primary
   torsion modules", for `p` prime to `ℓ`, is replaced by
   `ProPInvariantsExactStatement` for smooth representations over a ring `R`
   in which `p` is a unit, such as `ℤ/ℓ^mℤ` for `p ≠ ℓ`. That proposition is
   not proved; every result here depends on the hypothesis `hP`. Only its
   surjectivity part is used, in the form of epimorphisms on invariants of the
   restrictions to `H` of smooth representations of `G`.
3. The surjectivity on invariants. Harris obtains "an `ℓ`-divisible system of
   finite-length complexes of `ℤ/ℓ^mℤ[S(ẽ)/H]`-modules, in the obvious sense"
   without stating that the projections stay surjective on `H`-invariants;
   reading this as the needed input, and deriving it from the exactness of
   invariants applied to the kernel sequence of each projection, is ours.
4. The hypotheses on `H`. Harris's `H` is open, normal and pro-`p` in `S(ẽ)`
   and acts trivially on the cohomology. Here `H` is normal and pro-`p`, and
   for the total systems of finite index (as in the InvariantTotal module); it
   need not be open, and the trivial action on cohomology is not used. The
   latter is what Harris uses for the quasi-isomorphism
   `G_m^•(U(ẽ)_F̄)^H ↪ G_m^•(U(ẽ)_F̄)`, which this module does not address.

The structure `IsProPSubgroup` is the formal counterpart of Serre's and
Harris's pro-`p` subgroups, and `epi_smoothQuotientInvariants_map` is the
surjectivity half of Harris's exactness assertion, conditional on `hP`. The
lemmas on systems and the abbreviations are derived.

## Scope

The module does not prove `ProPInvariantsExactStatement`, the exactness of
the invariants functor on short exact sequences beyond the surjectivity used
here, or the existence of an open normal pro-`p` subgroup acting trivially on
the cohomology. It proves no quasi-isomorphism: neither that of the inclusion
of `H`-invariants nor, for pro-`p` subgroups, that of the totalized
augmentation. It does not construct the direct limit over `H`, the
quasi-isomorphism (2.6), the isomorphism (2.7) or Lemma 2.8.

Source registrations: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`; Serre,
Galois Cohomology, `serre-1997-galois-cohomology`, SHA-256
`343aafc5fe7ebb6605effc6f6e09338f622bb977325e8cdd166152cbd6eb7cf2`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
