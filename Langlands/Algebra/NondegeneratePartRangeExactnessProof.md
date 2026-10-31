# Exactness of the actual original restrictions

Authors: Worker 6 and Worker 691. This module proves the exact published
closed proposition
`Langlands.Algebra.NondegeneratePartRangeExactnessStatement.{uA,uL,uM,uN}`
in `Langlands.Algebra.NondegeneratePartRangeExactnessStatements`, importing
that unchanged statement and its published dependencies. Worker 6 supplied
the proof draft; Worker 691 checked the original passages, prepared the
focused proof pair and verified its complete interfaces.

For any original intertwiner `f : NonUnitalModuleHom A L M` and vector
`m : nondegeneratePart hA M`, the named lemma
`NonUnitalModuleHom.mem_range_restrictNondegeneratePart_iff` identifies
membership in the actual restricted range with membership of `m.val` in
the original range. A restricted preimage supplies an ambient preimage by
forgetting its subtype membership. Conversely, choose an ambient preimage
`l` and an actual idempotent `e` fixing `m.val`. The vector `(e : A) • l`
is fixed by `e`, since `e * e = e`, so it belongs to the source's actual
nondegenerate part. Intertwining and the fixing equation give
`f ((e : A) • l) = (e : A) • f l = (e : A) • m.val = m.val`.
Subtype extensionality proves equality in the target part. No preimage is
chosen globally, and the original source action need not be nondegenerate.

`mem_kernel_restrictNondegeneratePart_iff` identifies vanishing under the
restricted map with original vanishing, using the value projection in one
direction and subtype extensionality in the other. Stable-subgroup
extensionality, these two membership equivalences, and the original
range-kernel equality prove the named
`range_restrictNondegeneratePart_eq_kernel`. The closed theorem
`nondegeneratePartRangeExactnessStatement` introduces exactly the target's
quantified data and applies that lemma. It has no extra premise or parameter.
The range membership equivalence also shows that original surjections remain
surjections on the parts. Original injections remain injections by forgetting
subtype membership and applying the original injectivity.

The ring and all three carriers have independent universes. A complete
unapplied function type checks the named equality-preservation lemma;
the exact closed theorem is used at arbitrary universes and at both
alternating unequal assignments `(0,1,0,1)` and `(1,0,1,0)`. The statement and
proof use the published original actions, intertwiners, stable range, stable
kernel and restriction. They impose no unit-action, nontriviality, field,
commutativity, finite-generation or dimension condition. Zero rings, zero
carriers and degenerate actions are included. There is no assumed closure,
abelian, additive-functor or categorical exactness certificate.

The governing original is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Original module conventions are printed pp.5–6/PDF11–12. The nondegenerate
part is in I.1.2, printed p.7/PDF13. The implemented idempotent-adjusted lift
is precisely the proof of part-functor exactness at printed p.8/PDF14,
expressed with the published actual stable subgroups. Worker 691 read the
original PDF11–14 and visually checked PDF14. The registered supplementary
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was read at PDF1–3 and PDF18–19; these consulted pages give no correction
to this argument and do not replace the governing 2026 original. The membership,
injectivity and surjectivity interfaces are internal reusable consequences
of that argument. The source discrepancy concerning the unrestricted
abelian-subcategory criterion is not used. Categorical preservation of
ShortComplex.Exact by the actual inclusion and part functor, abelianness,
adjunctions, completion and scalar comparisons remain separate obligations.
