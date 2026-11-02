# Renard II.2.2: local vanishing and relative support closedness

Worker 633 implemented this proof and its explanation. Worker 6 supplied the
source audit, focused interface and representative-based proof route.

The theorem `Langlands.Sheaf.Renard.germSupportClosedness.{u,v}` proves the
unchanged published
`Langlands.Sheaf.Renard.GermSupportClosednessStatement.{u,v}`. It includes
raw local vanishing, raw relative support closedness, and their two
normalized specializations.

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, II.2.2, printed p.37 /
one-based PDF p.43. The registered original is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
PDF pp.43–44 were read directly. The supplementary 2010-edition
*Corrections et compléments*, registered as
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was checked on PDF pp.2–3. Those pages correct preceding formulas and do
not change this support proposition. The 2026 original governs this proof.

Renard defines support as the literal set of nonzero stalk values and
proves that it is closed in the section's domain. The implementation
follows that local argument on the published `GermSections F U` carrier.
The extension from the source's sheaf input to arbitrary raw presheaves,
the explicit contained basis-neighborhood interface, and the aggregate
are internal strengthening and packaging already present in the target.

`rawGermLocalVanishing` starts with an original germ section `s` and a
point `x : U` such that `s.val x = 0`. Its local-representability witness
`s.property x` supplies a basis neighborhood `W` of `x`, an inclusion
`W.obj ≤ U`, and an original section `t : Sections F W` representing
`s` throughout `W`. At `x`, the germ of `t` equals the germ of the zero
original section, since `rawGerm_zero` identifies the latter with zero.

The imported, published `rawGerm_eq_iff` compares those two original
sections on the same `W`. It returns a common smaller basis neighborhood
`V` containing `x` and equality of their restrictions there. Since
restriction is additive, the restriction of the zero section is zero.
Thus the restriction of `t` to `V` is zero. The inclusion of `V` into
`W`, composed with the local witness's inclusion into `U`, supplies the
required actual containment `V.obj ≤ U`.

For every `y ∈ V.obj`, the original representation equation identifies
`s.val ⟨y, hVU hy⟩` with the germ of `t` on `W`. The theorem
`rawGerm_restriction` identifies that germ with the germ of the
restriction on `V`. That restriction is zero, so `rawGerm_zero` proves
that the same section `s` vanishes at every point of `V`. No replacement
section or equality of arbitrary original sections is used.

`rawGermRelativeSupportClosedness` proves that the complement of
`germSupport s : Set U` is open. A point in that complement has value
zero. Applying local vanishing gives the contained basis neighborhood
`V`. Its inverse image under the actual inclusion
`Subtype.val : U → X` is open in the subtype topology, contains the
chosen point, and lies in the support complement because every value
there is zero. Mathlib's `isOpen_iff_forall_mem_open` assembles these
neighborhoods into an open complement; `isOpen_compl_iff` then gives
closedness. This proves relative closedness in `U`.

`normalizedGermLocalVanishing` and
`normalizedGermRelativeSupportClosedness` apply the two raw theorems to
precisely `F.obj`. Their section carriers, germ values and support are
unchanged. Finally `germSupportClosedness` quantifies the space, its
supplied topology and chosen basis and assembles the four families in
the target's specified order.

The space universe `u` and original-section universe `v` remain
independent. The imported stalk and germ-section carriers retain their
existing universe `max u v`. The proof assumes neither normalization
for the raw inputs nor any sheaf separation property. It uses equality
of two germs at one point to obtain equality after a smaller
restriction; it never tries to detect equality of original presheaf
sections from all their germs. The basis need not be closed under
intersections, since `rawGerm_eq_iff` returns a basis refinement.

There is no nonempty-domain assumption. When `U` is empty, local
vanishing has no point to consider, and the relative-support proof's
pointwise openness criterion is vacuous. The same argument covers an
empty space and any allowed empty basis, whether or not the basis
contains the empty open. Zero section groups are also allowed.

The statement and its imports are unchanged. This unit proves only
the four-part local-vanishing and relative-closedness target. It does
not construct compact-section groups, zero extension, exhaustion,
canonical-unit comparisons, or an ambient closedness theorem.
