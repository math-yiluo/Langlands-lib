# Compactness of adelic points of a proper scheme

`Langlands.Global.AdelicSpreadCompactnessStatement` is the conjunction of the
function-field and number-field compactness propositions. It expresses the
first consequence in Conrad, *Weil and Grothendieck approaches to adelic points*
(2011), printed p.11, Proposition 4.4: the actual adelic point space of a proper
scheme over a global field is compact.

Both clauses quantify a finite-type arithmetic model X at any finite initial
level S, a scheme Y over the original field, and an actual generic-fibre
isomorphism e to Y. The topology is precisely the transported arithmetic final
topology `curvePlaceSpreadAdelePointTopology` or
`numberFieldSpreadAdelePointTopology`, and the carrier is the actual relative
spectrum-morphism point space over the full adele ring. The sole additional
geometric assumption is properness of the structure morphism of Y. X need not
be separated or proper. No compactness or model replacement is assumed.

The function-field clause retains finite constants, the specified rational-function
action and compatible scalar tower, and possibly inseparable extensions. The
number-field clause retains every infinite completion. Both permit nonaffine
schemes, empty initial sets and arbitrary common universe u. Conrad's convention
uses nonempty function-field levels; nonempty superlevels are cofinal, so including
an empty initial level yields the same final topology.

The supplied model gives finite type of Y by base change and its isomorphism;
properness also implies finite type and separatedness of Y directly. The derived
formulation permits any supplied spread by the topology independence in Conrad's
construction, printed pp.5–6 Theorem 3.4 and Remark 3.5, and p.9 section 4.
Compactness follows by applying the proper-map assertion to the structure map
and observing that Spec F has one adelic point. This file states that consequence;
eventual stabilization of arithmetic stages is a separate target.
