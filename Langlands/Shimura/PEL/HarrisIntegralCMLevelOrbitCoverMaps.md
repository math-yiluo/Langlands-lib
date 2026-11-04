# Maps of finite-etale Harris monodromy orbit covers

This internal construction uses the actual integral-action family and finite raw
monodromy orbits from `HarrisIntegralCMLevelOrbitCovers`. Its cover constructions
retain the explicit nonemptiness premise for the unchanged level tower at one
level, the connected locally noetherian base, the algebraically closed point
field, and the earlier monodromy prerequisites. The action transporter and its
laws need only the inherited finite-orbit hypotheses.

`harrisIntegralCMFiniteOrbitCoverMap` lifts a morphism between the actual finite
continuous orbit actions by the inverse of `continuousActionFunctor s hs`.
The functor is an equivalence by the proved
`geometricContinuousActionEquivalence s hs`; it is not assumed as additional
data. Its object choices agree with the already selected orbit covers.
The `_action` theorem expresses the resulting action map by conjugation with
the selected action isomorphisms. The `_naturality` theorem cancels the target
inverse isomorphism, and `_fiber` evaluates that identity on an actual geometric
lift. The inverse functor's identity and composition laws give `_id` and `_comp`.

`harrisIntegralCMFiniteOrbitTransportActionMap` restricts the original raw
Harris translation, using the element and transporter condition of
`(hodgeLevelFunctor D C).map f`, to the actual orbit subtypes. Its target is
specified by a raw class `r` and an equality that the translation sends `q`
to `r`. Commutation with monodromy shows that this restricted map is equivariant.
The original translation identity and composition laws prove the corresponding
action-map laws. The composition theorem quantifies the intermediate and final
classes and their prescribed-image equalities.

`harrisIntegralCMFiniteOrbitCoverTransport` lifts that same action transporter
to an actual morphism of the selected finite-etale covers over the fixed base.
Its `_fiber` theorem recovers the original raw Harris translation under the
actual geometric-fibre comparisons. Its `_point` theorem then shows that it
carries the distinguished geometric lift of `q` to that of `r`. The action-map
and general cover-map laws imply the cover transporter's identity and
composition laws.

The provenance is internal: these constructions specialize the proved
finite-etale equivalence and the existing raw Harris transporter, without
adding a literature assertion. They concern individual finite monodromy
orbits over one fixed test scheme. They do not establish representability of
the whole raw level set, a normalized CM moduli comparison, or the host
division-case representability statement.
