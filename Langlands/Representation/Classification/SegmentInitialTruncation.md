# One-step initial segment truncation

Authors: Worker 700 and Worker 904. Worker 700 wrote the shared draft with the
constructors, the singleton/nonempty computation lemmas and the single-segment
degree identity. Worker 904 added the list case lemmas, the append and
membership lemmas and the list degree identity.

For any prime `p`, p-adic field `F : PadicField.{uF} p` and supplied topology
`T : F.TopologicalData`, this module constructs the one-step initial truncation
of a segment. The carrier universe `uV` is independent of `uF`. All
declarations below are in namespace `Langlands.PadicField.TopologicalData.Segment`.

## The nonempty helper

`dropLastNonempty Δ h`, for `h : 1 < Δ.length`, is the segment with the base of
`Δ` and length `Δ.length - 1`. Its rank is unchanged. The lemmas
`dropLastNonempty_base`, `dropLastNonempty_length`,
`dropLastNonempty_rank` and `dropLastNonempty_member` are the corresponding
computation identities. The member identity holds for every natural position
`i`. Membership in the support of the shorter segment also requires
`i < Δ.length - 1`. `dropLastNonempty_degree_add_rank` proves

```
(Δ.dropLastNonempty h).degree + Δ.rank = Δ.degree,
```

that is, `(m - 1) * r + r = m * r` for `m = Δ.length ≥ 2` and `r = Δ.rank`.

## The optional truncation

`dropLast Δ : Option (Segment T)` returns `some (Δ.dropLastNonempty h)` when
the length is greater than one and `none` for a singleton. The empty result is
the option `none`; there is no length-zero `Segment`. The lemmas
`dropLast_of_one_lt`, `dropLast_eq_none_iff` (`Δ.dropLast = none ↔ Δ.length = 1`)
and `dropLast_of_length_eq_one` give these two cases. The empty option counts as
degree zero in `dropLast_degree_add_rank`, which proves

```
((Δ.dropLast.map Segment.degree).getD 0) + Δ.rank = Δ.degree.
```

Its proof splits the two length cases. The nonempty case is
`dropLastNonempty_degree_add_rank`. In the singleton case both sides equal
`Δ.rank`.

## The list wrapper

`dropLastList l` is exactly `l.filterMap Segment.dropLast`. It keeps the order of
the supplied list and keeps repeated surviving terms. It omits exactly the
terms of length one. The lemmas are:

- `dropLastList_nil`: the empty list maps to the empty list.
- `dropLastList_cons`: the recursive step, a match on `Δ.dropLast`.
- `dropLastList_cons_of_one_lt`: the case `1 < Δ.length` of that step.
- `dropLastList_cons_of_length_eq_one`: the case `Δ.length = 1` of that step.
- `dropLastList_append`: the operation commutes with list concatenation.
- `mem_dropLastList`: `Γ` lies in `dropLastList l` if and only if
  `Δ.dropLast = some Γ` for some `Δ` in `l`.
- `dropLastList_degree_add_rank`: proves

  ```
  ((dropLastList l).map Segment.degree).sum + (l.map Segment.rank).sum
    = (l.map Segment.degree).sum.
  ```

  The proof is by induction on `l`, using `dropLast_degree_add_rank` for the head.

## Source and provenance

The original construction is in Zelevinsky, *Induced representations of
reductive p-adic groups II. On irreducible representations of GL(n)*, Ann. Sci.
ENS (4) 13 (1980), §3.5, printed p.182 / PDF page 19: for a segment
`Δ = [ρ, ρ']`, `Δ⁻ = Δ \ {ρ'}`, and `Δ⁻ = ∅` if `Δ = {ρ}`. The registered source
is `zelevinsky-1980-induced-ii`, SHA256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`. Worker 700
and Worker 904 each read that page as extracted text and as a rendered image. No
errata file for this source was found in the Library or project notes.

The existing segment `[ρ, ν^(m-1) ρ]` has base `ρ` and length `m`. Deleting its
end `ν^(m-1) ρ` therefore keeps the base and lowers the length by one. The
length-based `Option` encoding follows from that encoding and from §3.5. The
list wrapper `dropLastList` and all computation lemmas are internal
constructions derived from §3.5 and the existing segment encoding; Zelevinsky
does not state them in this form.

## Scope

The only project import is `Langlands.Representation.Classification.Segments`.
This module proves no equality of support sets after deletion, no preservation
of nonprecedence and no statement about derivatives of representations. In
particular it does not formalize Theorem 3.5 of the source. Reading deletion of
the last position as deletion of a unique support element requires
integral-twist freeness, which this module does not use. No classification,
existence or exhaustion theorem is imported or assumed.
