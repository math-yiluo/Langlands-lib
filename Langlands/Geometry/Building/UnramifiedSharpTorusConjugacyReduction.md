# Conditional assembly of unramified sharp torus conjugacy

`unramifiedSharpTorusConjugacyReduction.{u}` proves the exact proposition
`UnramifiedSharpTorusConjugacyReductionStatement.{u}` by the implementation
described below. Its four structural inputs remain explicit premises.

This internal reduction assembles the exact proposition
`UnramifiedSharpTorusConjugacyStatement.{u}` from four explicit structural
inputs. It is not an unconditional proof of that proposition.

`exists_cover_conjugacy_of_quasi_split_maximal_tori` works over any field
`k : Type u`. From each supplied maximally split maximal torus, it extracts an
actual ambient maximal split torus and its actual factorization through that
maximal torus. The premise `QuasiSplitMaximalTorusCentralizerStatement`
identifies the original maximal torus inclusion with a representative of the
whole centralizer of its contained split torus. The imported
`exists_cover_conjugacy_of_maximal_split_centralizers` then uses ordinary
maximal split torus conjugacy and the simply connected centralizer product.
It returns a point in the actual rational image of the supplied cover and a
group-scheme isomorphism between the original supplied torus presentations,
with the required commuting square.

`unramifiedSharpTorusConjugacy_of_structure` specializes this argument to
`UnramifiedClosure F` for every nonarchimedean local field `F : Type u`.
The fourth premise, `UnramifiedQuasiSplitStatement`, says that every connected
reductive group over that actual field is quasi-split. The supplied
derived-cover hypothesis provides the
connected reductivity needed to apply it. No new premise is inserted into the
published target: all four inputs are visible parameters of this conditional
theorem, whose conclusion is exactly the original target proposition.

The four inputs are ordinary maximal split torus conjugacy, the simply
connected centralizer product, the quasi-split centralizer identification,
and quasi-splitness over the maximal unramified extension. None is proved by
this module. In particular, successful compilation of this reduction does not
discharge the host proof task.

The provenance is an explicit assembly of the structural route in
Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Corollary 2.3.8,
printed p.81 (PDF p.112), Fact 2.6.22 and Lemma 2.6.24, printed pp.104–105
(PDF pp.135–136), and Remark 2.6.25(2) on printed p.105. The source is
registered as `kaletha-prasad-2023-bruhat-tits-new-approach`. The official
2024 corrections, `kaletha-prasad-2024-corrections`, Section 2.6, PDF pp.24–25,
add Henselian and perfect-residue hypotheses to the valued-field discussion.
The conditional field input is retained for the actual unramified local-field
setting, without assuming those field properties as new hypotheses of the
published target.
