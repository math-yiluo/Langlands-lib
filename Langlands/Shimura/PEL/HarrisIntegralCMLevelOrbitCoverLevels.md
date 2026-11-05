# Actual raw levels on the selected Harris orbit covers

This internal construction starts with the same universe-zero arithmetic data,
actual abelian family, dual witness, polarization map and integral endomorphism
action as `HarrisIntegralCMLevelRestriction`. It uses the supplied tensor,
duality, finite-Weil-transition, rational-adelic and torsion inputs. For a map
`f : T′ ⟶ T` of test schemes, the direct family's integral action is literally
`(relativeEndRestrict B f).comp a`. The successive family is obtained by first
pulling to `T` and then along `f.left`.

The general pullback construction retains quasi-separatedness of both test
schemes, finiteness of their geometric fibres, invertibility of all torsion
orders, and finiteness and etaleness of the roots-of-unity schemes on both bases.
A raw orbit class at `t ≫ f.left` need only be fixed by the image of
`fundamentalGroupMap`; invariance under the whole old fundamental group is
unnecessary. The actions are the existing Weil-frame right action and commuting
geometric monodromy action, with the original level subgroups.

`harrisIntegralCMImageFixedSuccessiveLevel` sends such a class through the
inverse pointed Weil-frame orbit base-change equivalence. It proves invariance
under the new fundamental group by applying the equivalence, using
`RightOrbit.map_smul` and the actual Weil-frame monodromy comparison, and then
using the input image-fixedness. Its `_val` theorem identifies the underlying
class with this exact inverse image.
`harrisIntegralCMImageFixedLevel` then applies the inverse of the existing
`harrisIntegralCMFullActionRestrictionLevelIso`. Its `_compare` theorem says
that comparison back to the successive family has exactly that same underlying
class; the proof uses the isomorphism's inverse law.

`harrisIntegralCMRestrictionRawClass` evaluates a direct fixed level back to
the old raw orbit set. It first compares to the successive family and then
applies the pointed orbit base-change equivalence. It retains an arbitrary old
point `s` and a propositional equality `t ≫ f.left = s`.
`harrisIntegralCMImageFixedLevelAt` provides the corresponding image-fixed
construction at `s`. Both definitions eliminate the point equality by
substitution. Its `_val` theorem proves that evaluation returns the exact
original class, using `_compare` and the orbit equivalence's inverse law.

The selected-cover specialization additionally retains the connected, locally
noetherian base and algebraically closed point field of
`HarrisIntegralCMLevelOrbitCovers`. Given a nonempty original tower at a level
`U`, a level `V` and a raw class `q` at `V`, write `Y` for the previously selected
actual finite-etale cover of `T.left` realizing the monodromy orbit of `q`, and
`x` for its distinguished lift. The separate generic lemma
`FiniteEtale.fundamentalGroupMap_fixes_lift` proves that the cover fundamental
group at `x.left` fixes `x` after mapping to the old group.
`harrisIntegralCMFiniteOrbitCover_image_fixes` applies the equivariance and
point-value theorems of the selected cover's fibre equivalence to deduce that
this image fixes the exact defining class `q`.

`harrisIntegralCMFiniteOrbitCoverLevel` applies the general construction with
`Tq = Over.mk (Y.obj.hom ≫ T.hom)`, the actual map `fq : Tq ⟶ T`, and point
equality `Over.w x`. The result is a fixed level at `V` on the direct pullback
of the original family to `Tq`, with the restricted integral action. This
specialization keeps quasi-separatedness of `Tq.left`, finiteness of fibres at
`x.left`, invertibility of torsion orders on `Y.obj.left`, and finiteness and
etaleness of its roots-of-unity schemes as explicit hypotheses; it does not
derive them here. `harrisIntegralCMFiniteOrbitCoverLevel_val` uses the general
recovery equation to show that evaluating this fixed level at the distinguished
lift returns the exact original `q` at `s`.

This is an internal specialization of the existing pointed Weil-frame
base-change and direct/successive comparison constructions. The stabilizer
argument uses actual finite-etale geometric lifts and does not assume
surjectivity of a fundamental-group map. These results do not identify the
full raw restriction presheaf with the equivariant-fibre-map presheaf, extend
the finite-etale-cover universal property to all test schemes, construct the
PEL moduli scheme, or prove smoothness, projectivity, output admissibility or
`DivisionCMRepresentabilityStatement`.
