# Quasi-splitness over the actual unramified closure

`Langlands.Geometry.Building.UnramifiedQuasiSplitStatement.{u}` is a
proposition-valued definition. This module supplies its statement, without a
proof.

For every nonarchimedean local field `F : Type u`, in either characteristic,
and every group scheme `H` over `Spec (UnramifiedClosure F)`, it asserts that
`IsConnectedReductive H` implies `IsQuasiSplit H`. The local-field premises
are exactly `[Field F] [ValuativeRel F] [TopologicalSpace F]
[IsNonarchimedeanLocalField F]`. The field is the published inertia fixed
field inside `SeparableClosure F`, not a separately supplied field or its
completion.

The conclusion uses the existing `IsQuasiSplit` predicate: it includes
connected reductivity and the existence of an actual field-defined
inclusion `B → H` which is Borel both over the field and after base change
to its algebraic closure. No cover, torus, choice of integral model,
quasi-splitness premise, or extra field property is supplied.

This is the local unramified specialization of Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), Corollary 2.3.8, printed p.81
(PDF p.112). There `K` is a discretely valued Henselian field with
algebraically closed residue field. Theorem 2.3.3(2), printed p.79
(PDF p.110), gives quasi-splitness for fields of dimension at most one;
Corollary 2.3.7 supplies that dimension bound in the Henselian setting.
Example 2.3.2(2), on printed p.79, also explicitly includes the maximal
unramified extension of a local field in its examples of `C₁` fields.
Theorem 2.3.3 does not require the field to be perfect when the group is
reductive, so the present statement retains local fields of positive
characteristic.

The official 2024 corrections, Section 2.6, PDF pp.24–25, add Henselian
and perfect-residue hypotheses for the later valued-group discussion.
They do not change the cited Section 2.3 results. Here the Henselian,
discrete-valuation and algebraically closed residue-field properties of
the actual `UnramifiedClosure F` must be proved or imported in a proof of
this statement. Their conjunction alone is not a Lean proof of
quasi-splitness: the reductive-group theorem remains an obligation.

The statement isolates the field-specific input used in the proof of
`UnramifiedSharpTorusConjugacyStatement`. It does not assert torus
conjugacy, sharp conjugacy under a simply connected cover, or the
identification of maximal-split centralizers with maximal tori.
