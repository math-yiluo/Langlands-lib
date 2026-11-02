# All-test relative root subgroup functors

This construction belongs to Worker 1263's relative-root task. It works with the
Library's actual group schemes `Grp (Over B)` and morphisms of all schemes over
an arbitrary base `B`. It makes no field, reductivity, splitness, smoothness,
primitivity, or representability assumption. The intended relative-root case is
a maximal split torus in a connected reductive group over any field.

The originals are Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
registered as `kaletha-prasad-2023-bruhat-tits-new-approach`, §2.6.3 and §2.6.8
(printed pp.94–95; PDF pp.125–126), and Proposition 2.11.9 with Definition
2.11.10 (printed pp.133–134; PDF pp.164–165); and Conrad–Gabber–Prasad,
*Pseudo-reductive Groups*, second edition (2015), registered as
`conrad-gabber-prasad-2015-pseudo-reductive`, Proposition 3.3.6 and its proof
(printed pp.109–110; PDF pp.135–136). The registered KP corrections of
1 November 2024 were checked at PDF p.25. Their Section 2.11 changes concern
notation in Proposition 2.11.1, without changing these constructions.

For an actual character `a : S → Gm`, `characterKernel a` is the Library's
scheme-theoretic kernel, with inclusion `characterKernelι a`. Nothing asserts
that it is smooth. The source's example in characteristic two has a factor
μ₂. `kernelCentralizer i a` uses the existing all-refinement fixed subgroup
of conjugation restricted to this actual kernel. The implemented membership
lemma identifies it with commutation against every kernel point on every
refinement, including nonreduced test schemes.

The source constructs Uₐ by descending the action of S on its kernel
centralizer to S/ker(a) ≅ Gm, then taking the identity-limit dynamic subgroup.
We give an equivalent intrinsic orbit-extension construction whose definition
does not require the centralizer to have a chosen representative. For
`g : T → G`, `orbit i g : T × S → G` is conjugation by the universal S-point.
`IsOrbitExtension i a g e` says that the actual map `e : T × A¹ → G` pulls back
along `(t,s) ↦ (t,a(s))` to this orbit. `subgroup i a` consists of such points
having an extension with value 1 at zero. Every product, inverse, and
restriction is obtained by the corresponding operation on these actual
extension maps. The Lean proofs implement exactly those operations; no test
is restricted to a field or an affine scheme. Equivalence with the source
construction under the appropriate closed representation and fpqc premises
is a separate structural comparison obligation, not a theorem of this file.

For a group scheme `C` and inclusion `j` already representing the actual kernel
centralizer, `centralizerAction` reuses `onRepresentedFixedSubgroup` to construct
the torus action. Its kernel acts trivially by the public restriction theorem.
If the character map is quasi-compact, flat and surjective, `quotientAction`
reuses the public fpqc action-descent construction to obtain the actual Gm
action on `C`; `quotientAction_restrict` proves the required recovery law.
These conditional constructions do not assert that a representative or the
fpqc premises have been supplied in the intended relative-root case.

The direct orbit construction and the conditional action bundles are internal
implementations of the cited source route. The file does not prove closed
representability, smoothness, connectedness, split unipotence, uniqueness,
Lie weight formulas, or the root-system axioms. Those remain separate targets.
