# Sharp conjugacy over the maximal unramified extension

`Langlands.Geometry.Building.UnramifiedSharpTorusConjugacyStatement.{u}` is
a statement, with no proof supplied in this module. It isolates the structural
conjugacy input used in the independence part of Kaletha–Prasad Lemma 2.6.24.

Let `F : Type u` be any nonarchimedean local field, in either characteristic,
and let `K = UnramifiedClosure F` be the published inertia fixed field inside
`SeparableClosure F`. For an actual simply connected cover `π : C → D` of
the derived subgroup `d : D → H`, and any two maximally split maximal torus
inclusions `i : T → H` and `i' : T' → H`, the statement asserts that there
are an actual point `g ∈ H(K)^♮` and an actual group-scheme isomorphism
`e : T ≅ T'` with

`i ≫ (H.innerIso g).hom = e.hom ≫ i'`.

Here `H(K)^♮` is exactly the published `simplyConnectedImage d π`, the
range of `C(K) → H(K)`. Membership is part of the conclusion. The
`IsSimplyConnectedDerivedCover` premise includes connected reductivity of
`H`; no independent existence of a cover is asserted. The tori, their
inclusions and the cover are arbitrary data satisfying the stated geometric
properties. No splitting field, valuation of a torus point, or norm subgroup
occurs in the statement.

This is a derived specialization of the source's minimal Levi conjugacy
input, rather than a quotation of the whole independence lemma. In
Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Lemma 2.6.24,
printed p.105 (PDF p.136), the proof uses conjugacy of minimal Levi
subgroups under the simply connected group. Over `K` the connected
reductive group is quasi-split (Corollary 2.3.8), so maximally split maximal
tori are minimal Levi subgroups, as also explained in Remark 2.6.25(2) on
the same page. Writing conjugacy as an isomorphism commuting with the two
inclusions avoids requiring the two presentations of a torus to coincide.
The source's simply connected conjugating point maps to the displayed
element of `simplyConnectedImage d π`.

The official 2024 corrections, Section 2.6, PDF pp.24–25, add the
Henselian and perfect-residue hypotheses before Definition 2.6.20; the
present statement is restricted to the source's actual unramified local
field setting. Proving its field properties and the sharp conjugacy
conclusion remains the proof obligation. This module does not infer sharp
conjugacy merely from the existing statement of ordinary rational conjugacy
of maximal split tori.
