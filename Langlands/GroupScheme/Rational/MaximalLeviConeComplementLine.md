# Missed directions on a central-annihilator line

This internal module reduces the published `MaximalLeviConeComplementStatement.{u}` to one
linear-algebra property of the split component. That property is where the maximality of
the parabolic enters. The module does not prove the property, and so it does not prove the
unconditional target.

## The two propositions

`MaximalLeviCentralLineStatement` has exactly the data and hypotheses of the target, up to
the nonzero real character `x : Vstar A` that vanishes on every cocharacter `ν` of `A`
for which `ν ≫ a ≫ l ≫ p` is central in `G`. These are: an arbitrary field, a connected
reductive `G`, an actual parabolic `p : P ⟶ G` that is not an isomorphism and is maximal
in the target's sense, a rational Levi `l : M ⟶ P`, and a split component `a : A ⟶ M`.
For these data the statement asserts that every `y : Vstar A` vanishing on the same
central cocharacters lies in `Submodule.span ℝ {x}`. In other words, the annihilator in
`Vstar A` of the central cocharacters is the line through `x`. In the source situation
(Renard VII.1.3, quoted in the target statement's documentation) this is the fact that
`A_M / A_G` is one-dimensional for a maximal Levi `M`. The present module only uses it as
a hypothesis.

`MaximalLeviConeComplementFromLine` is the implication
`MaximalLeviCentralLineStatement.{u} → MaximalLeviConeComplementStatement.{u}`. The
theorem `MaximalLeviConeComplementLine.maximalLeviConeComplement_of_line` proves it.

## Proof

The main theorem is `MaximalLeviConeComplementLine.range_eq_of_line`. It assumes
`[IsAffineHom G.X.hom] [Smooth G.X.hom]`, a connected reductive `G`,
`range (l ≫ p) ≠ ⊤`, and the line hypothesis for the composite `a ≫ l ≫ p`. It then takes
two parabolics `q₁, q₂` with Levis `lQ₁, lQ₂` from `M`, geometric unipotent radicals
`rQ₁, rQ₂`, and compatible root presentations `pres₁, pres₂` for `a`, with
`lQᵢ ≫ qᵢ = l ≫ p` and `x` outside both positive cones. Its conclusion is
`range q₁ = range q₂` and `range (rQ₁ ≫ q₁) = range (rQ₂ ≫ q₂)`. Maximality, `x ≠ 0` and
the vanishing of `x` on central cocharacters are not used here. The final theorem only
passes them to the line hypothesis.

1. *Restricted roots lie on the line.* `latticePairing_restrict_eq_zero_of_isCentral`
   restricts a relative root `β` of a torus `i : T ⟶ G` along a factorization
   `f ≫ i = m`. The restriction `f ≫ β` pairs to zero with every cocharacter of `A` that is
   central through `m`. This follows from the published `root_restrict_eq_zero_of_isCentral`
   and `RelativeRoot.latticePairing_restrict_cocharacterMapInt`. With the line hypothesis,
   `exists_smul_eq_of_line` writes every such `1 ⊗ (f ≫ β)` as `c • x`.

2. *Some restricted simple root exists.* `range_comp_ne_top_of_not_isIso` derives
   `range (l ≫ p) ≠ ⊤` from closedness of `p` and `¬ IsIso p`. A full-range monomorphism
   is identified with the identity through `isoOfIsRepresentedBy`. This argument is
   adapted from Worker 1785's private `isIso_of_full_range` in
   `MaximalLeviDynamicReduction`. `ParabolicRootPresentation.restrictedRoots_nonempty`
   then argues by contradiction. Suppose no simple relative root restricts nontrivially to
   `A`. Then the split-component cocharacter `ζ` of the presentation pairs to zero with
   every simple root (`isStandard_splitComponentCocharacter`). By
   `relativeRootNegation` and
   `relativeRoots_subset_addSubgroupClosure_simpleRelativeRoots`, `ζ` also pairs to zero
   with every relative root. `rootAnnihilatorCentrality` makes `ζ` central. Then
   `levi_eq_splitComponentCocharacter` and `isCentral_iff_dynamicCentralizer_eq_top`
   make the Levi image `⊤`, which is a contradiction.

3. *`x` is negative on each defining cocharacter.*
   `ParabolicRootPresentation.splitComponentEvaluation_neg_of_line` proves
   `splitComponentEvaluation x < 0` for a presentation whose positive cone misses `x`.
   Pick a restricted root `β₀ = c₀ • x`. Its evaluation is positive
   (`splitComponentEvaluation_pos_of_mem_restrictedRoots`), so the evaluation of `x` is
   nonzero. Suppose it were positive. The sum of all restricted roots lies in the positive
   cone and, by step 1, equals `t • x`. Its evaluation is positive
   (`splitComponentEvaluation_pos_of_mem_positiveCone`), which forces `t > 0`. Then
   `x = t⁻¹ • (sum)` lies in the cone (`smul_mem_positiveCone`), which contradicts the
   hypothesis.

4. *Root signs agree on one torus.* Work on the maximal split torus `T₁` of `pres₁`. Both
   split-component cocharacters `ζ₁, ζ₂` map into `T₁` with the same ambient composites
   (`groupHom_cocharacterMapInt_comp`, using `hc₁, hc₂`). By step 1, every relative root
   `α` of `T₁` pairs with the images of `ζ₁` and `ζ₂` as `c * ⟨x, ζ₁⟩` and
   `c * ⟨x, ζ₂⟩` for one real `c`. Both evaluations of `x` are negative (step 3), so the
   two pairings are nonnegative together and positive together.

5. *Conclusion.* The published `relativeRootSignInclusions` on `T₁` turns these sign
   implications, in both directions, into inclusions of the dynamic parabolics and of the
   dynamic unipotent subgroups of the two cocharacters. The published
   `parabolic_eq_splitComponentCocharacter` and `range_comp_radical_eq` identify these with
   `range qᵢ` and `range (rQᵢ ≫ qᵢ)`.

`maximalLeviConeComplement_of_line` introduces the target's binders and installs the
instances `hG.isAffineHom` and `hG.smooth`. It applies `range_eq_of_line`, taking
`range (l ≫ p) ≠ ⊤` from step 2 and the line hypothesis from
`MaximalLeviCentralLineStatement`.

## Provenance

The propositions and the proof are internal to this development. They are derived from the
published declarations named above: relative-root sign inclusions, relative-root negation,
root-annihilator centrality, the closure of relative roots under simple roots, the
split-component cocharacter and cone evaluations of `ParabolicRootPresentation`, and the
radical comparison `range_comp_radical_eq`. No external literature assertion and no
unproved structural proposition is used. The only retained premise is
`MaximalLeviCentralLineStatement`, which appears as the explicit antecedent of
`MaximalLeviConeComplementFromLine`.
