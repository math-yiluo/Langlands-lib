# Berkovich's comparison `H^q_c(X{G}, F) ≅ H^q_c(X, b^*F)` (étale)

Author: Worker 16.

This module defines one proposition,
`Langlands.Cohomology.AnalyticEtaleCompactComparison.AnalyticEtaleCompactComparisonStatement`.
It is the first assertion of Berkovich's Corollary 1.5.2(i): if a topological
group `G` acts continuously on a Hausdorff analytic space `X`, then for every
étale `G`-sheaf `F` the comparison maps `H^q_c(X{G}, F) → H^q_c(X, b^*F)` are
isomorphisms in every degree `q`. It is a theorem-statement definition, not a
proof. The isomorphism is the conclusion; it is not supplied as data or as a
hypothesis. The comparison map itself is Worker 26's published construction
`etaleCompactComparison`.

The Library takes compact supports in the `L`-valued points of `X` for a
normed field `L`, while Berkovich takes them in all points of `X`. Worker 26's
Markdown for `AnalyticEtaleComparison` shows that the comparison map is not an
isomorphism in general when some point of `X` underlies no `L`-valued point.
The proposition therefore adds the hypothesis that every point of `X` underlies
an `L`-valued point. Under it the Library's compact supports agree with
Berkovich's (see "Why the proposition is expected to hold").

## Objects

All objects are imported from Worker 26's published module
`Langlands.Sheaf.Equivariant.AnalyticEtaleComparison` (namespace
`Langlands.Sheaf.Equivariant.Analytic`) and the modules it builds on, mainly
Worker 26's `AnalyticCompactSupport`, `AnalyticEtaleCompactCohomology` and
`AnalyticGSheaves`, and Worker 21's analytic spaces, field-valued points, étale
site and continuous actions.

- `K : Type u` is a complete ultrametric normed field (`NormedField`,
  `IsUltrametricDist`, `CompleteSpace`). `X` is an object of Worker 21's
  category of analytic spaces `LocalizedCategory.{u, v, v} (K := K)`. Its
  underlying topological space is `localizedSpaceFunctor.obj X`, written `|X|`
  below.
- `L : Type uL` is a normed field with `[NormedAlgebra K L]`.
  `(localizedFieldPointFunctor L).obj X` is the set of `L`-valued points of `X`
  (Worker 21's `FieldValuedPoints`): a point of `|X|` together with a
  compatible family of `K`-algebra characters into `L`, one for each chart
  containing the point, whose norms are the seminorm of the point.
  `pointProjection L X` sends an `L`-valued point to its underlying point of
  `|X|`.
- `h : ∀ x, EtaleSite.PointAxioms L x` is the hypothesis, needed to form the
  comparison map, that every `L`-valued point of `X` satisfies Worker 21's
  point axioms: the category of elements of its fibre functor on the étale
  site is cofiltered, and every element over an object lifts to a member of
  each covering sieve. With `h`, the `L`-valued points form the family of
  points `etalePoints L h` of the étale site of `X`. Worker 21's unproved
  `EtaleSite.GeometricPointStatement` asserts these axioms for every complete,
  ultrametric, algebraically closed `L`.
- `G : Type z` is a topological group (`IsTopologicalGroup`) and
  `ρ : G →* Aut X` an action of `G` on `X` by automorphisms. `Aut X` consists
  of automorphisms of `X` in the category of `K`-analytic spaces, that is,
  over `K`.
- `R : Type (max u (v + 1) uL)` is a commutative ring. Sheaves take values in
  `R`-modules. This coefficient universe is the one of Worker 26's derived
  functors.
- `EtaleGSheaf ρ (ModuleCat R)` is Worker 26's category of étale `G`-sheaves:
  sheaves on the twisted étale site of `X` (Berkovich's `G^d`-sheaves) whose
  sections are locally discrete for `distinguishedLiftSystem ρ`. For every
  section `s` over `U`, the arrows into `U` that factor through a
  distinguished étale object `V` on which the restriction of `s` is fixed by an
  open subgroup acting through a lift of the action form a covering sieve.
- Supports and compactness. For a module sheaf `F` on the étale site of `X`
  and `s ∈ F(X)`, the support of `s` is the set of `L`-valued points `x` at
  which the germ of `s` in the stalk of `etalePoints L h` is nonzero. The
  `L`-valued points carry `pointTopology L X`, the topology induced from `|X|`
  by `pointProjection L X`. The section `s` is compactly supported when its
  support lies in a compact set of `L`-valued points.
- `etaleGSheafCompactCohomology L ρ h R q` is Berkovich's `H^q_c(X{G}, F)`. It
  is the `q`-th right derived functor of `etaleGSheafCompactSections L ρ h R`,
  Berkovich's `Γ_{c,X{G}}`: the smooth part of the representation of `G` on
  the compactly supported global sections of `F`. Derived functors are
  computed with injective resolutions in `EtaleGSheaf ρ (ModuleCat R)`, and the
  values are smooth representations of `G`.
- `etaleCompactCohomology L h R q` is `H^q_c(X, -)`, the `q`-th right derived
  functor of `etaleCompactSections L h R`, the compactly supported global
  sections of `R`-module sheaves on Worker 21's étale site of `X`. Its
  coverings are the families of étale morphisms whose point maps are jointly
  surjective.
- `etaleGSheafRestriction ρ R` is Berkovich's `b^*`: the inclusion of étale
  `G`-sheaves into sheaves on the twisted étale site, followed by restriction
  to the étale site of `X`, which forgets the action of `G`. It is exact.
- `etaleCompactComparison L ρ h R q` is the comparison
  `H^q_c(X{G}, F) → H^q_c(X, b^*F)`. It is a natural transformation from
  `etaleGSheafCompactCohomology L ρ h R q ⋙ smoothForget R G` (the underlying
  modules of `H^q_c(X{G}, F)`) to
  `etaleGSheafRestriction ρ R ⋙ etaleCompactCohomology L h R q`. Worker 26
  defines it as the base change, along the exact functors `b^*` and
  `smoothForget`, of `etaleCompactInclusion`, the inclusion
  `Γ_{c,X{G}}(F) ⊆ Γ_c(X, b^*F)` of smooth compactly supported sections into
  all compactly supported sections.
- `T2Space (localizedSpaceFunctor.obj X)` says that `|X|` is Hausdorff.
- `Function.Surjective (pointProjection L X)` says that every point of `|X|`
  underlies an `L`-valued point.
- `IsContinuousAction ρ`, from Worker 21's `ContinuousAnalyticAction`, is
  Berkovich's continuity of an action: for every test triple `τ` (Berkovich's
  `ε ∈ E(X)`), the preimage under `ρ` of the set of automorphisms within `τ` of
  the identity is a neighbourhood of `1` in `G`.

## The proposition

| Declaration | Asserted conclusion |
| --- | --- |
| `AnalyticEtaleCompactComparisonStatement L X h G ρ R` | If `|X|` is Hausdorff, `pointProjection L X` is surjective and `IsContinuousAction ρ` holds, then for every `q : ℕ` the natural transformation `etaleCompactComparison L ρ h R q` is an isomorphism (`IsIso`). |

`IsIso` of a natural transformation means that it is a natural isomorphism.
So the proposition asserts that each map `H^q_c(X{G}, F) → H^q_c(X, b^*F)` is
a bijection, for every étale `G`-sheaf `F` of `R`-modules. These maps are
natural in `F` and are the comparison maps that Worker 26 constructed.
Isomorphisms are not merely asserted to exist.

The three conditions are hypotheses of the proposition, not binders of the
definition. The binders `L`, `h`, `[Small.{max u (v + 1) uL} G]` and
`[(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]`
are needed to form the comparison map. They are the same as in Worker 26's
declarations.

- `L` and `h` give the points in which supports are taken.
- `[Small.{max u (v + 1) uL} G]` is a size condition. It makes the twisted
  étale site essentially small, which the published sheafification and
  enough-injectives results on that site use. It holds, for example, when `G`
  lies in a universe at most `max u (v + 1) uL`.
- `[(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]`
  is Worker 26's class from `LocalActionSmoothPart`. It has two fields. First,
  every arrow of the twisted étale site between objects with admissible local
  actions is compatible with the two actions on open subgroups
  (`IsRestrictionEquivariant`), so that restriction along it preserves
  discreteness of sections. Second, every cone over a cospan is covered by
  objects with admissible local actions that map to the cospan
  (`fiberRefinementSieve`). Worker 26 uses it to make étale `G`-sheaves of
  modules an abelian category with enough injectives. It is not proved in the
  Library. Worker 26's module `AnalyticEtaleRefinements` derives it from three
  conditions on the étale site of `X`: distinguished étale neighbourhoods of
  points, lifts of the action to distinguished étale objects, and
  compatibility of lifts along arrows over `X`. Geometrically these are
  Berkovich's statements on p.7 and p.8, which rest on his Key Lemma on lifts.
  If the class failed, the proposition could not be formed for that action.

## Original source

Berkovich, *Etale equivariant sheaves on p-adic analytic spaces* (unfinished
1995–1996 manuscript), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`
(folder SHA-256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`, member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`).
Printed page numbers equal PDF page numbers.

- Corollary 1.5.2(i), pp.11–12: "For any étale abelian sheaf `F` on `X(G)`
  there are canonical isomorphisms `H^q_c(X{G}, F) ⥲ H^q_c(X, b^*F)`,
  `g ≥ 0` [sic, for `q ≥ 0`]. In particular, the canonical action of `G` on
  the groups `H^q_c(X, b^*F)` is discrete and there is a spectral sequence
  `E_2^{p,q} = H^p(G, H^q_c(X, b^*F)) ⟹ H^{p+q}_c(X(G), F)`." This module
  states the first sentence.
- The proof, p.12: "The case `q = 0` in (i) (resp. (ii)) follows from the fact
  that every element of `H^0_c(X, b^*F)` is fixed by an open subgroup of `G`
  (resp. is trivial), and therefore the general case follows from
  Proposition 1.5.1."
- §1.5, p.10: "Let `X` be a `G`-space." This is the standing assumption of
  §1.5. The Godement resolution `C^·(F)` of an étale abelian sheaf on `X(G)` is
  built there from a set `I` with a surjection onto `X` and geometric points
  over its images. Proposition 1.5.1, p.10: "For any `F ∈ X(G)~_ét` and
  `m ≥ 0`, `b^*(C^m(F))` is a soft sheaf on `X_ét`."
- §1.5, p.11: "The support of an element `f ∈ F(X(G))` is the set
  `Supp(f) = {x ∈ X | f_x ≠ 0}`, where `f_x` is the image of `f` in `F_x`. It
  is a closed subset of `X`." Then
  `Γ_{c,X(G)}(F) := {f ∈ F(X(G)) | Supp(f) is compact}`,
  `Γ_{c,X{G}}(F) := lim_→ Γ_{c,X(N)}(F)` over open subgroups `N`, and
  `H^q_c(X{G}, F)` are the higher direct images of `Γ_{c,X{G}}`.
- §1.1, p.1: "In what follows all analytic spaces considered are assumed to be
  Hausdorff." Hence the hypothesis `T2Space (localizedSpaceFunctor.obj X)`.
- §1.1, pp.1–2: the topology on the automorphism group `G(X)` is defined by the
  subgroups `G_ε(X)`, `ε ∈ E(X)`. "We say that the action of a topological
  group `G` on an analytic space is continuous if the induced homomorphism
  `G → G(X)` is continuous." "An analytic space `X` endowed with a continuous
  action of a topological group `G` will be called a `G`-space." Hence
  `IsContinuousAction ρ`. For a homomorphism of groups, continuity is
  continuity at `1`, which is what `IsContinuousAction` states.
- §1.4, pp.7–8: distinguished étale morphisms and their lifted actions (p.7),
  Definition 1.4.1, and the characterization on p.8: "an étale `G^d`-sheaf `F`
  is a `G`-sheaf if and only if for any étale morphism `U → X` and any element
  `f ∈ F(U)` each point of `U` has a distinguished open neighborhood `𝒰` such
  that the stabilizer of `f|𝒰` is open in `G_𝒰`". Worker 26's `EtaleGSheaf`
  models this characterization.

## Correspondence and modelling choices

- Berkovich's étale abelian sheaves on `X(G)` are modelled by Worker 26's
  étale `G`-sheaves `EtaleGSheaf ρ`, through Berkovich's Theorem 1.4.2 and the
  characterization on p.8, as in all of Worker 26's étale modules. Theorem
  1.4.2 is not formalized.
- Berkovich works with abelian sheaves. Here sheaves take values in
  `R`-modules for an arbitrary commutative ring `R` in the coefficient universe;
  abelian sheaves are the case `R = ULift ℤ`. The statement for all `R` is the
  natural generalization. Berkovich's argument (below) uses nothing specific
  to abelian groups.
- Berkovich takes supports in all points of `X`, through the stalks at
  geometric points. The Library takes them in `L`-valued points, with the
  topology induced from `|X|` (Worker 26's `AnalyticCompactSupport`). The
  hypothesis that `pointProjection L X` is surjective is ours. It is not in
  Berkovich, and is what makes the two notions of compact support agree.
  Without it the degree-zero comparison can fail. Worker 26's Markdown for
  `AnalyticEtaleComparison` (section "Supports in `L`-valued points") gives the
  example `K = ℚ_p`, `L = ℂ_p`, `G = ℤ_p` permuting the copies of a disjoint
  union of closed discs, and a sheaf concentrated at their Gauss points. No
  `ℂ_p`-valued point lies over a Gauss point, so a global section that is
  nonzero at infinitely many Gauss points has empty `L`-support but is not
  fixed by any open subgroup.
- Surjectivity holds when, for every point `y` of `|X|`, the completed residue
  field `ℋ(y)` admits an isometric `K`-embedding into `L`. Such an embedding
  gives an `L`-valued point over `y` by composing the canonical characters of
  the charts into `ℋ(y)` (Worker 21's `FieldValuedPoints` Markdown, which does
  not formalize these characters). This remark is not used in the statement.
- The hypotheses are Berkovich's (`X` is a Hausdorff `G`-space) together with
  the surjectivity hypothesis above. The binders `L`, `h` and the two instance
  binders are needed only to form the comparison map. They are not hypotheses
  of Berkovich's corollary.
- Base field. Berkovich's automorphisms of a `k`-analytic space may induce a
  nontrivial isometric automorphism of `k` (§1.1, p.1: "If `X` is
  `k`-analytic, then such an automorphism induces an isometric automorphism of
  the field `k`."). In `LocalizedCategory (K := K)` all morphisms are over the
  fixed field `K`, so `Aut X` consists of `K`-linear automorphisms. The
  proposition therefore covers only actions that fix the base field.
- Only the first sentence of Corollary 1.5.2(i) is stated. The discreteness of
  the action of `G` on `H^q_c(X, b^*F)` is not stated separately. The spectral
  sequence is not stated: the Markdown of the published
  `Langlands.Cohomology.EquivariantComposite.Statement` shows that its
  ordinary-topological analogue fails for `G = ℤ` acting on `X = ℤ` by
  translation, and states its composite-functor form for compact `G` only.
  Part (ii) of the corollary,
  on ringed spaces, is not stated.

## Why the proposition is expected to hold

The following argument is ours, and follows Berkovich's two-line proof. It
uses facts from Berkovich's theory that the Library does not prove: étale
morphisms are open maps with discrete fibres, open immersions are étale, and a
sheaf on the étale site whose stalks at all geometric points vanish is zero.

1. L-supports see Berkovich supports. Let `s ∈ F(X)` for a module sheaf `F` on
   the étale site of `X`, let `x` be an `L`-valued point and `y` its
   underlying point. If the germ of `s` at `x` vanishes, then `s` vanishes on
   some étale `U → X` carrying an `L`-valued point over `x`. Its underlying
   point lies over `y`, so the geometric stalk `s_y` vanishes. Conversely, if
   `s_y` vanishes, then `s` vanishes on some étale `U → X` with a point `u`
   over `y`. Since `|X|` is Hausdorff, `X ∖ {y}` is open, and `U → X` together
   with the open immersion `X ∖ {y} → X` is a covering. The second point axiom
   for `x`, applied to the sieve they generate, gives an `L`-valued point over
   `x` on a member of that sieve. It cannot lie on an object mapping to
   `X ∖ {y}`, so it lies on an object over `U`, on which `s` vanishes. Hence
   the germ of `s` at `x` vanishes. So the Library support of `s` is the
   preimage of Berkovich's `Supp(s)` under `pointProjection L X`, and by
   surjectivity its image is exactly `Supp(s)`. The published
   `exists_isCompact_superset_iff_of_surjective` then shows that `s` is
   compactly supported in the Library's sense exactly when `Supp(s)` lies in a
   compact subset of `|X|`. Since `Supp(s)` is closed and `|X|` is Hausdorff,
   this holds exactly when `Supp(s)` is compact. So the Library's
   `Γ_c(X, -)` and `Γ_{c,X{G}}` agree with Berkovich's.
2. Degree zero. The degree-zero comparison is the inclusion of the smooth
   compactly supported sections into all compactly supported sections of
   `b^*F`. Let `s` be a compactly supported global section of an étale
   `G`-sheaf `F`, with compact support `C ⊆ |X|`. Local discreteness gives
   distinguished étale objects `V` with open images covering `|X|`, on each of
   which `s` is fixed by an open subgroup `H_V` acting through a lift.
   Finitely many `V_1, …, V_n` have images covering `C`. Let `H` be the
   intersection of the `H_{V_i}`, an open subgroup, and `W` the union of the
   images of the `V_i`. Each `g ∈ H` lifts to every `V_i`, so it maps `W` to
   itself and `g • s` agrees with `s` on every `V_i`. The support `C'` of
   `g • s` is the translate of `C` by `g` or by `g⁻¹`, depending on
   conventions; it is compact and lies in `W`, since `H` is a group. The `V_i`
   together with the open set `X ∖ (C ∪ C')` cover `X`, and both `s` and
   `g • s` vanish on the latter, since their stalks vanish there. By the sheaf
   condition `g • s = s`. So
   every compactly supported global section is smooth, which is Berkovich's
   degree-zero fact, and the degree-zero comparison is an isomorphism.
3. Higher degrees. For an étale `G`-sheaf `F`, the Godement resolution of §1.5
   embeds `F` into `C^0(F)`, and by Proposition 1.5.1 `b^*(C^0(F))` is soft.
   Berkovich's proof relies on soft sheaves being acyclic for compactly
   supported cohomology. He refers to [Ber3] (Berkovich, *Vanishing cycles for
   formal schemes*, Invent. Math. 115 (1994)), §3, for softness on p.10; that
   paper was not consulted for this module. Since `b^*` is exact, the functors
   `H^q_c(X, b^*(-))` form a δ-functor on étale `G`-sheaves that is
   effaceable in positive degrees, hence universal. The underlying modules of
   `H^q_c(X{G}, -)` are the right derived functors of `Γ_{c,X{G}}` followed by
   the exact forgetful functor, so they also form a universal δ-functor. By
   step 2 the two agree in degree zero through the inclusion. The comparison
   maps are a morphism of δ-functors extending that inclusion (a standard
   property of such base-change maps, which the Library does not record), so
   they are isomorphisms in all degrees. Proposition 1.5.1 is where Berkovich
   uses that `X` is a `G`-space: its proof shrinks `G` to open subgroups of
   the groups `G_U` of p.7.

The Library does not yet have the Godement resolution of §1.5,
Proposition 1.5.1 or the acyclicity of soft étale sheaves.

## Relation to other statements

The ordinary comparison `H^q(X{G}, F) ≅ H^q(X, b^*F)` for compact `X` is the
companion statement
`Langlands.Cohomology.AnalyticEtaleGlobalComparison.AnalyticEtaleGlobalComparisonStatement`
(Berkovich's Theorem 1.6.1(ii), étale case). Neither statement is derived from
the other here. The quasi-étale analogue of this proposition with supports in
`L`-valued points is not stated: the coverage note records a counterexample on
the quasi-étale model, whose topos has rank-two points that no `L`-valued
point detects.

## Role in the Harris framework

This proposition is a theorem statement for Task 16, "Formalize the Harris and
Berkovich cohomological theorem-statement framework". That task covers
Berkovich's equivariant-sheaf comparisons as part of the geometric and
cohomological input to Harris's weak automorphic induction. The task's
coverage note `notes/henniart/harris-cohomology-coverage.md` lists which
comparisons are stated and which remain open. No other Library statement uses
this proposition yet.
