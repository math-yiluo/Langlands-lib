# The Euler-characteristic square formula for the Mumford map of an ample line bundle

`Langlands.AbelianScheme.AlgClosedFieldAmpleMumfordEulerSquareStatement` is a
universe-polymorphic `Prop`-valued definition. It states the Riemann–Roch
degree formula `χ(L)^2 = deg φ_L` of Milne, *Abelian Varieties*, Theorem
13.3 (a), and of Mumford, Fogarty and Kirwan, *Geometric Invariant Theory*,
Proposition 6.13 (iii). It concerns an ample line bundle `L` on an abelian
scheme over an algebraically closed field. Here `φ_L` is the actual Library
Mumford map `mumfordSchemeMapOfLineBundle`, and its degree is Mathlib's
native rank function `Scheme.Hom.finrank`. The module supplies no proof and
adds no axiom.

## Statement

Fix the following data:

- a proof `preservation` of the published proposition
  `Langlands.Scheme.Modules.pullbackTensorComparisonIsIsoStatement`;
- a proof `square` of the published proposition
  `Langlands.AbelianScheme.MumfordBundlePicardZeroStatement`;
- a field `K : Type u` with `IsAlgClosed K`;
- `A : AbelianScheme (Spec (CommRingCat.of K))` and `hA : HasDualScheme A`;
- a line bundle `L : LineBundle A.X.left` with `L.IsAmple`;
- a proof `h : HasFiniteCohomology A.X.hom L.obj`;
- a line bundle `B` on `Spec K` with an evaluation isomorphism
  `evaluationB : e^*L ⊗ B ≅ O_{Spec K}`, where `e = unitSection A`;
- a line bundle `M` on `A.X.left` with an evaluation isomorphism
  `evaluation : N ⊗ M ≅ O_A`, where `N` is the normalized bundle
  `LineBundle.normalize preservation A.X.hom (unitSection A)
  (unitSection_comp A) L B evaluationB` (its carrier is `L ⊗ π^*B`, with
  `π = A.X.hom`);
- a morphism `f : A.X ⟶ dualScheme A hA` over `Spec K` with
  `f = mumfordSchemeMapOfLineBundle preservation A L B evaluationB M evaluation square hA`.

If the underlying scheme morphism `f.left` is finite and flat, then for
every point `y` of the scheme `(dualScheme A hA).left`,

```text
eulerCharacteristic A.X.hom L.obj h ^ 2 = (f.left.finrank y : ℤ).
```

In words: the square of the Euler characteristic of `L` equals the rank of
`f_*O_A` at every point of the chosen dual. The rank is the same at every
point.

The morphism `f` is quantified only to name the Mumford map. The equation
premise determines it uniquely, so `f` is not arbitrary data. This is the
same device as in the published
`Langlands.AbelianScheme.HasAmpleMumfordPresentation`
(`Langlands/AlgebraicGeometry/Picard/AmpleMumfordBaseChange.lean`). The
inputs `B`, `evaluationB`, `M` and `evaluation` are universally quantified,
so the conclusion is asserted for every admissible choice of normalization
data. It does not depend on a chosen normalization (see "Normalization
independence" below).

The hypotheses do not include the Euler-square equality, the vanishing of
higher cohomology, the value of `dim H^0`, the dimension of `A`, a
polarization, a degree value or any numerical data. `h` only says that the
cohomology is finite-dimensional and bounded. It is quantified explicitly
because `eulerCharacteristic` takes it as an argument. The finite and flat
premises are permitted by the task. They make `Scheme.Hom.finrank` the rank
of a locally free sheaf.

## Complete checked type

The source declaration is

```lean
def AlgClosedFieldAmpleMumfordEulerSquareStatement : Prop :=
  ∀ (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    (square : MumfordBundlePicardZeroStatement.{u})
    (K : Type u) [Field K] [IsAlgClosed K]
    (A : AbelianScheme (Spec (CommRingCat.of K))) (hA : HasDualScheme A)
    (L : LineBundle A.X.left), L.IsAmple →
    ∀ (h : HasFiniteCohomology A.X.hom L.obj)
      (B : LineBundle (Spec (CommRingCat.of K)))
      (evaluationB : tensorObj ((Scheme.Modules.pullback (unitSection A)).obj L.obj) B.obj ≅
        structureSheaf (Spec (CommRingCat.of K)))
      (M : LineBundle A.X.left)
      (evaluation : tensorObj (LineBundle.normalize preservation A.X.hom (unitSection A)
        (unitSection_comp A) L B evaluationB).obj.carrier M.obj ≅ structureSheaf A.X.left)
      (f : A.X ⟶ dualScheme A hA),
      f = mumfordSchemeMapOfLineBundle preservation A L B evaluationB M evaluation square hA →
        IsFinite f.left → Flat f.left →
          ∀ y : (dualScheme A hA).left,
            eulerCharacteristic A.X.hom L.obj h ^ 2 = (f.left.finrank y : ℤ)
```

inside `namespace Langlands.AbelianScheme`, with
`open CategoryTheory AlgebraicGeometry`,
`open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules` and
`open Langlands.AlgebraicGeometry.Modules.DerivedSections`. It imports
`Langlands.AlgebraicGeometry.Picard.Ample`,
`Langlands.AlgebraicGeometry.Picard.MumfordLineBundle`,
`Langlands.AlgebraicGeometry.Modules.EulerCharacteristic`,
`Mathlib.AlgebraicGeometry.Morphisms.FlatRank` and
`Mathlib.FieldTheory.IsAlgClosed.Basic`.

In the approved environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, on
Library commit `dad4d948`, the module compiles with no errors or warnings.
`#check` reports type `Prop`. `#print axioms` reports only `propext`,
`Classical.choice` and `Quot.sound`. With `pp.fieldNotation false`,
`pp.proofs true` and `pp.funBinderTypes true`, `#print` reports:

```text
def Langlands.AbelianScheme.AlgClosedFieldAmpleMumfordEulerSquareStatement.{u} : Prop :=
∀ (preservation : Langlands.Scheme.Modules.pullbackTensorComparisonIsIsoStatement)
  (square : Langlands.AbelianScheme.MumfordBundlePicardZeroStatement) (K : Type u) [inst : Field K] [IsAlgClosed K]
  (A : Langlands.AbelianScheme (AlgebraicGeometry.Spec ↧K)) (hA : Langlands.AbelianScheme.HasDualScheme A)
  (L :
    Langlands.AlgebraicGeometry.Picard.LineBundle
      (CategoryTheory.Over.left
        (CategoryTheory.Grp.X (Langlands.CommGroupScheme.toGrp (Langlands.AbelianScheme.toCommGroupScheme A))))),
  Langlands.AlgebraicGeometry.Picard.LineBundle.IsAmple L →
    ∀
      (h :
        Langlands.AlgebraicGeometry.Modules.DerivedSections.HasFiniteCohomology
          (CategoryTheory.Over.hom
            (CategoryTheory.Grp.X (Langlands.CommGroupScheme.toGrp (Langlands.AbelianScheme.toCommGroupScheme A))))
          (CategoryTheory.ObjectProperty.FullSubcategory.obj L))
      (B : Langlands.AlgebraicGeometry.Picard.LineBundle (AlgebraicGeometry.Spec ↧K))
      (evaluationB :
        Langlands.Scheme.Modules.tensorObj
            (CategoryTheory.Functor.obj
              (AlgebraicGeometry.Scheme.Modules.pullback (Langlands.AbelianScheme.unitSection A))
              (CategoryTheory.ObjectProperty.FullSubcategory.obj L))
            (CategoryTheory.ObjectProperty.FullSubcategory.obj B) ≅
          Langlands.Scheme.Modules.structureSheaf (AlgebraicGeometry.Spec ↧K))
      (M :
        Langlands.AlgebraicGeometry.Picard.LineBundle
          (CategoryTheory.Over.left
            (CategoryTheory.Grp.X (Langlands.CommGroupScheme.toGrp (Langlands.AbelianScheme.toCommGroupScheme A)))))
      (evaluation :
        Langlands.Scheme.Modules.tensorObj
            (Langlands.SchemeModule.RigidifiedModule.carrier
              (CategoryTheory.ObjectProperty.FullSubcategory.obj
                (Langlands.AlgebraicGeometry.Picard.LineBundle.normalize
                  (fun {X Y : AlgebraicGeometry.Scheme} => preservation)
                  (CategoryTheory.Over.hom
                    (CategoryTheory.Grp.X
                      (Langlands.CommGroupScheme.toGrp (Langlands.AbelianScheme.toCommGroupScheme A))))
                  (Langlands.AbelianScheme.unitSection A)
                  (Langlands.AbelianScheme.AlgClosedFieldAmpleMumfordEulerSquareStatement._proof_1 K A) L B
                  evaluationB)))
            (CategoryTheory.ObjectProperty.FullSubcategory.obj M) ≅
          Langlands.Scheme.Modules.structureSheaf
            (CategoryTheory.Over.left
              (CategoryTheory.Grp.X (Langlands.CommGroupScheme.toGrp (Langlands.AbelianScheme.toCommGroupScheme A)))))
      (f :
        CategoryTheory.Grp.X (Langlands.CommGroupScheme.toGrp (Langlands.AbelianScheme.toCommGroupScheme A)) ⟶
          Langlands.AbelianScheme.dualScheme A hA),
      f =
          Langlands.AbelianScheme.mumfordSchemeMapOfLineBundle (fun {X Y : AlgebraicGeometry.Scheme} => preservation) A
            L B evaluationB M evaluation square hA →
        AlgebraicGeometry.IsFinite (CategoryTheory.Over.Hom.left f) →
          AlgebraicGeometry.Flat (CategoryTheory.Over.Hom.left f) →
            ∀ (y : ↥(CategoryTheory.Over.left (Langlands.AbelianScheme.dualScheme A hA))),
              Langlands.AlgebraicGeometry.Modules.DerivedSections.eulerCharacteristic
                    (CategoryTheory.Over.hom
                      (CategoryTheory.Grp.X
                        (Langlands.CommGroupScheme.toGrp (Langlands.AbelianScheme.toCommGroupScheme A))))
                    (CategoryTheory.ObjectProperty.FullSubcategory.obj L) h ^
                  2 =
                ↑(AlgebraicGeometry.Scheme.Hom.finrank (CategoryTheory.Over.Hom.left f) y)
```

Here `↧K` is `CommRingCat.of K`, and `A.X` abbreviates
`Grp.X (CommGroupScheme.toGrp (toCommGroupScheme A))`. The term
`AlgClosedFieldAmpleMumfordEulerSquareStatement._proof_1 K A` is the
auxiliary theorem Lean generated for the source proof `unitSection_comp A`.
`#check` reports its type as
`∀ (K : Type u_1) [Field K] (A : AbelianScheme (Spec ↧K)),
unitSection A ≫ A.X.hom = 𝟙 (Spec ↧K)`. It is a proof of a proposition, so
the statement does not depend on which proof is used. The binder
`fun {X Y : Scheme} => preservation` is the elaborated form of
`preservation`, whose type has implicit binders `{X Y}`.

## Library objects used

The statement uses only published definitions. It adds no structure,
certificate, axiom, tensor product, inverse or choice of its own.

- `pullbackTensorComparisonIsIsoStatement` says the canonical comparison
  `f^*(F ⊗ G) → f^*F ⊗ f^*G` is invertible for every scheme morphism `f`.
  It is proved in the Library as
  `Langlands.Scheme.Modules.pullbackTensorComparisonIsIso`
  (`Langlands/AlgebraicGeometry/Modules/PullbackTensorProof.lean`).
- `MumfordBundlePicardZeroStatement` says that, over every base, the
  rigidified Mumford family `mumfordBundle A preservation L M evaluation`
  of a rigidified bundle `L` with inverse `M` satisfies
  `IsPicardZeroFamily`: every geometric fibre is invariant under every
  translation. This is the theorem-of-the-square input. The Library has
  only the conditional theorem
  `Langlands.AbelianScheme.MumfordPicardZero.mumfordBundlePicardZero_of_cube`,
  which derives it from `Langlands.GroupScheme.FieldCubePullbackStatement`
  and `FieldLineBundleTrivialityStatement`. It has no unconditional proof.
- `A : AbelianScheme S` is a commutative group scheme over `S` whose
  structure morphism `A.X.hom` is smooth, proper and geometrically
  connected. Here `S = Spec K`.
- `HasDualScheme A` is the proposition
  `∃ (P : Over S) (L : RigidifiedFamily A P), IsUniversalPicardZero A L`.
  `dualScheme A hA` and `poincareFamily A hA` are chosen from it by
  `Classical.choose`. The rigidified family lives on
  `(relativeSpace A.X.hom).obj P`, the fibre product with the parameter
  `P` as first factor, and is rigidified along the unit section.
- `LineBundle X` is the full subcategory of actual `X.Modules` locally
  isomorphic to the structure sheaf. `L.obj` is the underlying module.
- `L.IsAmple` is the published ampleness predicate: `X` is compact, and
  every point lies in the generation open `L.sectionOpen s` of a section `s`
  of some positive actual tensor power `tensorPow L.obj n`, where that
  whole open is affine.
- `unitSection A : Spec K ⟶ A.X.left` is the underlying morphism of the
  identity rational point, and `unitSection_comp A` proves it is a section
  of `A.X.hom`.
- `LineBundle.normalize preservation A.X.hom (unitSection A)
  (unitSection_comp A) L B evaluationB` is the rigidified bundle with
  underlying line bundle `L ⊗ π^*B` and the rigidification
  `O_{Spec K} ≅ e^*(L ⊗ π^*B)` built from `evaluationB`
  (`Langlands/AlgebraicGeometry/Picard/LineBundleNormalization.lean`).
- `mumfordSchemeMapOfLineBundle preservation A L B evaluationB M evaluation
  square hA : A.X ⟶ dualScheme A hA` is the morphism over `Spec K`
  classifying the actual rigidified Mumford family
  `mumfordFamilyOfLineBundle` of the normalized bundle. By
  `mumfordFamilyOfLineBundle_forget`, the underlying bundle of that family
  is `(m^*(L ⊗ π^*B) ⊗ p_1^*M) ⊗ p_2^*M` on `A ×_S A`, with the first factor
  as parameter. `mumfordSchemeMapOfLineBundlePullbackIso` identifies the
  rigidified Poincaré pullback along this map with the family, and
  `mumfordSchemeMapOfLineBundle_unique` shows that any map with such an
  identification equals it
  (`Langlands/AlgebraicGeometry/Picard/MumfordLineBundle.lean`).
- `HasFiniteCohomology A.X.hom L.obj` says that every
  `(relativeCohomology A.X.hom n).obj L.obj` is a finite-dimensional
  `K`-vector space and that these vanish for `n` beyond some bound.
  `eulerCharacteristic A.X.hom L.obj h` is
  `∑ᶠ n, (-1)^n * finrank K ((relativeCohomology A.X.hom n).obj L.obj)`.
  Here `relativeCohomology A.X.hom n` is the `n`-th right-derived functor of
  `Scheme.Modules.pushforward A.X.hom ⋙ moduleSpecΓFunctor`, computed in
  the category of `O_A`-modules
  (`Langlands/AlgebraicGeometry/Modules/EulerCharacteristic.lean` and
  `DerivedSections.lean`; source: Stacks Project, tag 0BEI).
- `IsFinite` and `Flat` are Mathlib's morphism properties of the underlying
  scheme morphism `f.left`. `Scheme.Hom.finrank f.left y` is Mathlib's rank
  function `(dualScheme A hA).left → ℕ`
  (`Mathlib/AlgebraicGeometry/Morphisms/FlatRank.lean`).

## Source specialization

The statement is the special case "algebraically closed base field, ample line
bundle" of two published results.

**Milne.** J. S. Milne, *Abelian Varieties*, author corrected version of 2 January
2022 (registered source `milne-abelian-varieties-1986-author-2022`).

- Theorem 13.3 (PDF p.25). For an invertible sheaf `L` on an abelian variety `A`
  over a field `k`, write `χ(L) = Σ (-1)^i dim_k H^i(A, L)`. Part (a) reads "The
  degree of φ_L is χ(L)^2." The proof is the single line "Combine Mumford 1970, §16,
  p.150, with (4.2a)."
- The morphism `φ_L` (PDF p.17, end of §10). Milne forms
  `L* = m^*L ⊗ p^*L^{-1} ⊗ q^*L^{-1}` on `A × A`. Then `L*|{0}×A ≅ L ⊗ L^{-1}` is
  trivial, and `L*|A×{a} ≅ t_a^*L ⊗ L^{-1} = φ_L(a)`. For ample `L`, if the dual
  `(A^∨, P)` exists, "there is a unique isogeny φ: A → A^∨ such that
  (1 × φ)^*P = L*. Moreover φ = φ_L." So Milne's parameter is the **second**
  factor of `A × A`.
- Degree (PDF p.12, the paragraph after Proposition 8.1). The degree of an isogeny
  is the order of its kernel, "equivalently, it is the rank of f_*O_A as a locally
  free O_B-module". Proposition 8.1 (d) says that isogenies are finite, flat and
  surjective.

**GIT.** Mumford, Fogarty and Kirwan, *Geometric Invariant Theory*, third edition
(1994), Chapter 6 (registered source
`provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`).

- Definition 6.1 (PDF p.128, printed p.115). Over a noetherian base `S`, an abelian
  scheme is a smooth proper group scheme with geometrically connected fibres.
  Corollary 6.5 (PDF p.130, printed p.117) says abelian schemes are commutative.
  For a projective abelian scheme the dual is `X^ = Pic^τ(X/S)`. Corollary 6.8 (PDF
  p.131, printed p.118) shows that it is again a projective abelian scheme.
- `Λ(L)` (PDF p.133, printed p.120, Definition 6.2). The sheaf
  `μ^*L ⊗ p_1^*L^{-1} ⊗ p_2^*L^{-1}` on `X ×_S X`, "regarding X ×_S X as a scheme
  over X via p_1", defines an `X`-valued point of `Pic(X/S)`. That point lies in
  `Pic^τ(X/S)` and is a homomorphism `Λ(L): X → X^`. So GIT's parameter is the
  **first** factor.
- Proposition 6.13 (PDF p.136, printed p.123). Let `π: X → S` be a projective
  abelian scheme and `L` relatively ample for `π`. Then (i) `R^iπ_*(L) = 0` for
  `i > 0`; (ii) `π_*(L)` is locally free, of rank `r`; (iii) "Let Λ(L): X → X^ be
  the finite flat morphism defined by L. Then the degree of Λ(L), i.e. the rank of
  Λ(L)_*(O_X), is r^2." The proof says that over a field (ii) is vacuous and (iii)
  is due to Nishi. Its footnote adds that over a field (i), (iii) and (iv) are also
  proved in Mumford's *Abelian Varieties*, §16, 17.

**The specialization.** Take `S = Spec K` with `K` algebraically closed. By (i),
`H^i(X, L) = 0` for `i > 0`, so `χ(L) = dim_K H^0(X, L) = r`. Then (iii) gives
`deg Λ(L) = r^2 = χ(L)^2`. This is Milne's Theorem 13.3 (a) for ample `L` over `K`.
The Lean conclusion `eulerCharacteristic A.X.hom L.obj h ^ 2 = f.left.finrank y`
states this equality at every point `y` of the dual.

**Which factor is the parameter.** The Library family is parameter-first, like GIT's
and unlike Milne's. `mumfordSection` (in
`Langlands/AlgebraicGeometry/Picard/MumfordBundle.lean`) is "the section
`(id, e)` of the parameter-first family". By `mumfordFamilyOfLineBundle_forget`
(an `rfl` lemma), the underlying line bundle is
`(m^*(L ⊗ π^*B) ⊗ p_1^*M) ⊗ p_2^*M` on `A ×_S A`. Here `N = L ⊗ π^*B` is the
normalized bundle and `M` is a tensor inverse of `N`. The factor `p_1^*M` comes from
the parameter scheme, and twisting `L` by `π^*B` only adds a line bundle pulled back
from `S`. So the underlying bundle differs from GIT's
`μ^*L ⊗ p_1^*L^{-1} ⊗ p_2^*L^{-1}` only by a line bundle pulled back from the
parameter scheme. It therefore defines the same point of the relative Picard
functor, and the Library adds a rigidification along `(id, e)`. Restricting along
`x ↦ (a, x)` gives `t_a^*N ⊗ N^{-1}`, up to a line bundle constant in `x`; this is
`φ_L(a)`. Milne's second-factor convention gives the same map. The swap of factors
fixes `m` because the group law is commutative: the Library `AbelianScheme` bundles
a `CommGroupScheme`, and GIT proves commutativity in Corollary 6.5. The swap
exchanges `p_1` and `p_2`, and it carries Milne's rigidification along `{0} × A`
to the Library's along `(id, e)`. None of these comparisons is formalized; they
explain why the Lean conclusion is the source formula.

## Hypotheses and mismatches with the sources

1. **Field and line bundle.** Milne allows any field and any `L`. His convention for a
   non-isogeny, stated for endomorphisms (PDF p.21), is degree `0`. GIT allows a noetherian base, a projective
   abelian scheme and a relatively ample `L`. The statement takes an algebraically
   closed `K : Type u` of arbitrary characteristic and an ample `L`, so it is a
   special case of both. Library `LineBundle.IsAmple`
   (`Langlands/AlgebraicGeometry/Picard/Ample.lean`) is
   Stacks Definition 28.27.1 (tag 01PS), which is EGA II Definition 4.5.3. Milne's
   ampleness means that some power is very ample (PDF p.12, Remark 7.3). For proper
   `K`-schemes the two notions agree classically, but the Library does not formalize
   this comparison.
2. **Finite and flat are hypotheses.** `IsFinite f.left` and `Flat f.left` are
   premises here. In the sources they are conclusions: GIT 6.13 (iii) calls
   `Λ(L)` "the finite flat morphism defined by L", and Milne (PDF p.17 with
   Proposition 8.1 (d)) shows `φ_L` is an isogeny for ample `L`. So the Lean
   statement is weaker than the sources, as the objective permits. It asserts the
   degree formula only for maps that are finite and flat. Under these premises
   `Scheme.Hom.finrank` is the native degree (see the next section).
3. **Projectivity.** GIT 6.13 needs a projective abelian scheme. The Library
   `AbelianScheme S` (`Langlands/AbelianScheme/Basic.lean`) is a `CommGroupScheme` with
   `Smooth`, `IsProper` and `GeometricallyConnected` structure morphism. It assumes
   neither projectivity nor a noetherian base. Over a field, an abelian variety with
   an ample line bundle is projective classically. The Library does not formalize
   this.
4. **The dual.** `HasDualScheme A`
   (`Langlands/AlgebraicGeometry/Picard/DualScheme.lean`) asks for some
   `P : Over S` and a rigidified family on `P ×_S A` satisfying
   `IsUniversalPicardZero`. That predicate requires the family to be geometrically
   Picard zero, meaning its fibres at all geometric points `Spec K' → P` with
   `K' : Type u` algebraically closed are translation invariant. It also requires
   unique classification of such rigidified families over every test object
   `T : Over S`. `dualScheme A hA` is the `Classical.choose` witness. It is not
   required to be an abelian scheme, projective or reduced. Milne (PDF pp.15–16)
   requires `A^∨` to be an abelian variety. His universal property tests every
   `k`-scheme `T` and invertible sheaves `L` on `A × T` with `L|{0}×T` trivial and
   `L|A×{t}` in `Pic^0(A_{k(t)})`. By Milne's conventions (PDF p.2), a scheme
   over `k` is always of finite type, so his test schemes `T` are of finite type
   over `k`, while the Library tests every `T : Over S`. GIT uses
   `X^ = Pic^τ(X/S)`. The Library proves no isomorphism between `dualScheme A hA` and either source dual. Its
   `picardZeroComparisonIso`
   (`Langlands/AlgebraicGeometry/Picard/PicardZeroUniversalBundle.lean`) compares two
   universal witnesses, but it needs further stability and coherence inputs. Any
   such isomorphism would leave the degree unchanged:
   `Langlands.AbelianScheme.PolarizedFiniteLevel.finrank_comp_iso`
   (`Langlands/AbelianScheme/PolarizedFiniteLevel/Degree.lean`) proves
   `(f ≫ e.hom).finrank z = f.finrank (e.inv z)` for finite flat `f`.
5. **Prerequisite statements.** `preservation : pullbackTensorComparisonIsIsoStatement`
   is proved in the Library as `pullbackTensorComparisonIsIso`.
   `square : MumfordBundlePicardZeroStatement` is not proved at Library `dad4d948`.
   `mumfordBundlePicardZero_of_cube`
   (`Langlands/AlgebraicGeometry/Picard/MumfordBundlePicardZeroReduction.lean`)
   reduces it to the field cube statement plus field line-bundle triviality.
   `fieldCubePullbackOfIsomorphism`
   (`Langlands/AbelianScheme/FieldCubePullbackAssembly.lean`)
   reduces the field cube statement to `FieldCubeIsomorphismStatement`, which is
   still open. So `square` is a genuine premise. The objective allows it to be
   quantified. Both prerequisites, and `hA`, are propositions, so by proof
   irrelevance the map and `dualScheme A hA` do not depend on which proofs are
   supplied.
6. **Cohomology.** Milne's `χ(L)` uses `dim_k H^i(A, L)`. The Library's
   `eulerCharacteristic A.X.hom L.obj h`
   (`Langlands/AlgebraicGeometry/Modules/EulerCharacteristic.lean`) is the
   alternating sum of the `K`-dimensions of `relativeCohomology A.X.hom n L.obj`.
   These are the right derived functors of the relative global-sections functor on
   `O_X`-modules. `h : HasFiniteCohomology A.X.hom L.obj` asserts that every such
   module is finite-dimensional and that they vanish in high degree. It is a
   proposition, so the value of `eulerCharacteristic` does not depend on the proof.
   It is quantified, not replaced by numerical data. The published
   `smoothProperLineBundleEulerPolynomial` gives finiteness for every tensor power
   `tensorPow L.obj n`, which is how the parent task supplies `h`. This statement
   makes no claim about a comparison between `relativeCohomology` and
   abelian-sheaf cohomology.

## Native degree convention

The degree is Mathlib's `Scheme.Hom.finrank f.left y`
(`Mathlib/AlgebraicGeometry/Morphisms/FlatRank.lean`). It chooses an affine open
`Spec R` of the target containing `y` and pulls `f.left` back to it. The value is
`RingHom.finrank` of the resulting ring map at the prime `y`. That is
`Module.rankAtStalk`, the rank at `y` of the ring of global sections of the pullback
as an `R`-module. Mathlib's docstring describes it as "the rank of `f_* 𝒪_X` over `𝒪_Y`
at `y`" and notes that this is "sometimes also called the degree of a morphism in
the literature". Mathlib's TODO says that the relation to `f_* 𝒪_X` is not yet
formalized. This is the quantity in both sources: Milne's "rank of f_*O_A as a
locally free O_B-module" (PDF p.12) and GIT's "rank of Λ(L)_*(O_X)" (6.13 (iii)).

The function is defined for every morphism, but it has these properties only for
finite flat maps: independence of the chosen affine open, invariance under base
change (`finrank_pullback_snd`, `finrank_of_isPullback`) and local constancy
(`isLocallyConstant_finrank`, which also needs `LocallyOfFinitePresentation`). This
is why the statement assumes `IsFinite f.left` and `Flat f.left`. The conclusion
asserts the equality at every point `y`, so the degree is constant and equal to
`χ(L)^2`. In the Library's notation `HasConstantDegree f r` (`∀ y, f.finrank y = r`, in
`Langlands/AbelianScheme/PolarizedFiniteLevel/Degree.lean`), the conclusion says that `f.left` has constant
degree whose integer cast is `χ(L)^2`. Neither source needs a degree
convention for non-isogenies here: `L` is ample.

## Normalization independence

The Library's `mumfordSchemeMapOfLineBundle` uses four pieces of normalization data.
`B` is a line bundle on `Spec K` with
`evaluationB : e^*L ⊗ B ≅ 𝒪`, which makes `N = L ⊗ π^*B` rigidified along the unit
section `e`. `M` is a line bundle on `A` with `evaluation : N ⊗ M ≅ 𝒪`. The Library
Markdown of `MumfordLineBundle` says that the existence of inverses and independence
of these choices are not proved there.

**The statement does not need independence.** It quantifies over **all** `B`,
`evaluationB`, `M` and `evaluation`, and over every `f` equal to the resulting map.
So it claims the formula for every choice, and its truth does not rest on any
independence result. Independence only explains why the statement is about the
single map `φ_L` of the sources.

**The choices always exist.** The universal quantifier over normalization data is
never empty. `LineBundle.exists_tensorObj_iso_structureSheaf`
(`Langlands/AlgebraicGeometry/Picard/LineBundleDualEvaluation.lean`) says that every line bundle has a tensor
inverse, namely its dual. Applying it to `(LineBundle.pullback (unitSection A)).obj L`
gives `B` and `evaluationB`. Applying it to the underlying line bundle of the
normalized `N` gives `M` and `evaluation`. Worker 943 checked this two-step argument
in Lean against this declaration's module, over any base `S` (private check,
`lean_check` diagnostic `d59202b4-0d25-4e53-92b5-5029ed0f89fe`, 0 errors). The
check is not part of the submission.

**Mathematical argument for independence (not formalized).** Let
`(B, evaluationB, M, evaluation)` and `(B', evaluationB', M', evaluation')` be two
choices over `Spec K`.

- Every line bundle on `Spec K` is trivial (`fieldLineBundleTriviality`), so
  `B ≅ B'`. Hence `N ≅ N'` as line bundles. The two rigidifications differ by a unit
  of `K`, so after rescaling the isomorphism respects them.
- Both `M` and `M'` are tensor inverses of `N ≅ N'`, so `M ≅ M'`.
- These isomorphisms give an isomorphism between the underlying bundles of the two
  rigidified Mumford families on `A ×_K A`. Its failure to respect the
  rigidifications along `(id, e)` is a unit on the parameter scheme `A`. Rescaling
  by the pullback of that unit along `p_1` makes the isomorphism rigidified.
- The second map's Poincaré pullback is isomorphic to the second family
  (`mumfordSchemeMapOfLineBundlePullbackIso`), and hence to the first.
  `mumfordSchemeMapOfLineBundle_unique` then shows that the two maps are equal.

So, granted the premises, all choices give the same morphism `A.X ⟶ dualScheme A hA`.
For a fixed `K`, `A` and `hA`, quantifying over the choices is equivalent to stating
the formula for any single choice.

## Proof obligations for the later exact proof

After independent acceptance and publication, a separate exact-target proof
must have this entire named proposition as its type, with no extra outer
hypotheses. A conditional assembly that takes further propositions as
premises is not such a proof.

Milne proves Theorem 13.3 (a) by citing Mumford, *Abelian Varieties*,
§16, p.150, together with his own Theorem 4.2 (a), flat base change for the
cohomology of a proper flat family (Milne, PDF p.6). Read in context,
Theorem 4.2 (a) transfers cohomology dimensions along a field extension, so
over an algebraically closed field only Mumford's argument is needed. GIT
cites Nishi and Mumford, *Abelian Varieties*, §16–17. Of Mumford's book only
Chapter II (printed pp.39–87) is a registered source here, and it does not
contain §16. So the following outline of the standard argument is only a
guide, and any correct route is allowed. Write `g` for the
dimension, `Λ` for the Library Mumford family on `A × A` with parameter on
the first factor, `p_1, p_2` for the projections, and `P` for the Poincaré
family.

1. **Identify the Poincaré pullback.** Pulling `P` back along `f` in the
   parameter factor gives `Λ = (m^*(L ⊗ π^*B) ⊗ p_1^*M) ⊗ p_2^*M`, by
   `mumfordSchemeMapOfLineBundlePullbackIso`. Over a field, `π^*B` is
   trivial and `M ≅ L^{-1}`, so `Λ ≅ m^*L ⊗ p_1^*L^{-1} ⊗ p_2^*L^{-1}`.
2. **Compute directly.** `Λ ⊗ p_1^*L ≅ m^*L ⊗ p_2^*L^{-1}` is the pullback
   of `p_1^*L ⊗ p_2^*L^{-1}` along the shear `(x, y) ↦ (x + y, y)`, an
   automorphism of `A × A`. The Künneth formula gives
   `χ(A × A, Λ ⊗ p_1^*L) = χ(L) · χ(L^{-1})`. Serre duality with trivial
   canonical bundle gives `χ(L^{-1}) = (-1)^g χ(L)`.
3. **Compute through the dual.** For the Poincaré family, `R^i p_{1*} P`
   vanishes for `i ≠ g`, and `R^g p_{1*} P` is the skyscraper `κ(0)` at the
   origin of the dual. Since `f` is flat, base change gives
   `R^i p_{1*} Λ ≅ f^* R^i p_{1*} P`. The projection formula and the Leray
   spectral sequence then give
   `χ(A × A, Λ ⊗ p_1^*L) = (-1)^g · dim_K Γ(f^{-1}(0), O)`. For the finite
   flat `f`, that dimension is the rank of `f_*O_A` at the origin.
4. **Compare.** Hence `χ(L)^2 = f.left.finrank 0`. The rank of a finite
   flat morphism of finite presentation is locally constant
   (`Scheme.Hom.isLocallyConstant_finrank`), and the dual is connected, so
   the identity holds at every point `y`.

Read as a Library proof, this route needs at least the following, none of
which this module supplies:

- A Künneth formula for actual `relativeCohomology` on products over a
  field, and invariance of cohomology under automorphisms.
- Serre duality or an equivalent symmetry `χ(L^{-1}) = (-1)^g χ(L)`. The
  published `smoothProperLineBundleEulerPolynomial` gives finiteness and
  polynomial behaviour of `χ(L^{⊗ n})` for `n ≥ 0` only.
- Higher direct images along `p_1`, their flat base change, the projection
  formula and the Leray spectral sequence, all for actual
  `Scheme.Modules`.
- The direct images of the Poincaré family. This needs an identification of
  the chosen `dualScheme A hA` with the source dual, including its
  dimension and connectedness. The Library's `dualScheme` is only an object
  chosen from the representability proposition `hA`.
- The bridge between `Scheme.Hom.finrank` and the dimension of a fibre
  algebra of a finite flat morphism. Mathlib's `FlatRank.lean` lists the
  comparison with the rank of `f_*O_X` as future work.
- Identification of `eulerCharacteristic` with the alternating sum of the
  source's `H^i(A, L)`, and of the actual tensor products, pullbacks and
  inverse bundles with their source counterparts. The pullback-tensor
  comparison needed for this is `pullbackTensorComparisonIsIso`.

The theorem of the square is supplied by the quantified `square`, and the
pullback-tensor comparison by the quantified `preservation`. A proof must
use them, or published proofs, rather than new premises. Any substantial
missing construction must be split into definition, statement and proof
units, in that order.

## Scope

The statement covers every universe `u` and every algebraically closed
field in every characteristic. Algebraic closedness is the only condition on
`K`. It also covers dimension zero. Mathematically, there
`A.X.left ≅ Spec K`, every line bundle is trivial and ample with `χ = 1`,
and the Mumford map is an isomorphism onto the dual, of rank `1`. It adds no projectivity, symmetry,
polarization, separability, dimension or degree premise. The only
hypotheses beyond the task's quantified prerequisites are ampleness, the
finite-cohomology proof `h`, and the finite and flat premises on the Mumford
map.

The statement does not assert that the Mumford map of an ample bundle is
finite, flat or surjective, that `h` exists, that higher cohomology
vanishes, or any value of `χ(L)`. It does not compare Mumford maps for
different normalization data. It does not prove that `dualScheme A hA` is
isomorphic to a source dual abelian variety.

## Role and authorship

This statement is a prerequisite of task
`baec6a6d-fe08-417e-95fd-fb8e2291cb1d`, owned by Worker 689 and Worker 100.
That task proves
`Langlands.AbelianScheme.PolarizedFiniteLevel.CubicFibreCohomologyStatement`.
Its parent obtains `h` from `smoothProperLineBundleEulerPolynomial`. Its
owners keep ampleness of the cubic bundle, the identities `φ_L = 2λ` and
`φ_{L^3} = 6λ`, the native degree computation, finite cohomology, higher
vanishing, and the final assembly. This statement does not prove the
Euler-square formula. A separate proof task is to be published for it after
acceptance.

Worker 1029 wrote the Lean statement and the sections on the statement,
checked type, Library objects, proof obligations, scope and role. Worker 943
wrote the sections on source specialization, hypotheses and mismatches, the
native degree convention and normalization independence.
