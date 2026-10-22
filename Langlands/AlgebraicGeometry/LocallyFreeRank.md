# Fixed finite local rank of scheme modules

For a scheme `S : Scheme.{u}`, an actual module sheaf `M : S.Modules`, and
`n : ℕ`, `Langlands.Scheme.Modules.IsLocallyFreeOfRank M n` means that `M`
has local bases with exactly `n` elements on an open cover.

The definition refines Mathlib's `SheafOfModules.LocalGeneratorsData`.
Its data consist of covering opens `q.X i` and generating sections of the
restricted sheaves `M.over (q.X i)`. The condition `q.IsLocallyFreeData`
makes each canonical map from the free sheaf on these generators an
isomorphism. The additional condition requires each generator index type
to be equivalent to `Fin n`. The covering index and the section types lie
in universe `u`; the equivalences with `Fin n` allow finite bases in any
such universe.

This is the open-cover form of the Stacks Project, Definition 17.14.1(3),
tag 01C6, in Section 17.14, tag 01C5. Mathlib's
`Opens.coversTop_iff` identifies the site-cover condition
with an open cover. Its `Scheme.Modules.overEquiv` and `overFunctorEquiv`
identify the sheaf on the site over an open with restriction to the open
subscheme. Thus these are bases of the restricted sheaf, with linearity
and compatibility on all smaller opens.

`IsLocallyFreeOfRank.isLocallyFree` forgets the fixed basis size and gives
Mathlib's `SheafOfModules.IsLocallyFree`. `IsLocallyFreeOfRank.isFiniteType`
uses the equivalences with `Fin n` to make each local generator family
finite. `isLocallyFreeOfRank_free` applies the free sheaf's standard
generating sections and their restrictions, with index type
`ULift.{u} (Fin n)`. These are direct consequences of the definition and
Mathlib's implemented generating-section constructions.

The predicate prescribes one finite rank throughout the scheme. On the
empty scheme it does not assert uniqueness of that rank. It imposes no
nonemptiness, connectedness, smoothness, or affineness assumption. This
module supplies the rank predicate for later geometric statements; it
does not construct a Lie module or prove its local freeness.

Source: `stacks-local-freeness-invertibility-sections-2026-10-21`,
retained file `01C5.html`, Definition 17.14.1(1)–(3), especially (3).
The local-generator formulation and the three elementary compatibility
lemmas are the implementation used here.
