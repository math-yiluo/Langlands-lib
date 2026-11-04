# Actual fixed-model adelic point comparisons

This derived target specializes the published filtered-colimit comparison for
actual relative scheme points to the original arithmetic level systems. Its
source context is Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), printed p.6, equation (3.5.1), and printed p.9, the final
topology used at the beginning of section 4. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`.

Fix a finite set `S` and a scheme `X` over its outside-`S` integer ring. The
curve-place branch uses the actual discrete places of any field extension
`F/k`, with its given algebra structure. The number-field branch uses the full
adele ring of any number field, including every infinite factor. All levels
are finite supersets of `S`, with their original scalar actions and literal
coefficient inclusions. `S` may be empty, and the common universe is arbitrary.
No affineness or separation hypothesis is imposed on `X`.

Under **locally finite type** of the structure morphism of `X`, the canonical
map from the actual stage-point colimit to the fixed model's actual full-adele
points is injective. Two stage points have the same full-adele point exactly
when their images agree at some common finite superlevel. The target states
both the two-stage and the same-stage versions of this eventual equality
criterion. The maps in these criteria are the actual fixed-base algebra
inclusions, and coefficient change means precomposition with their spectra.

Under **locally finite presentation**, every full-adele point factors through
some finite superlevel. The canonical comparison is bijective and is a
homeomorphism for the two independently constructed final topologies. The
stage topology is transported by the actual base-change point equivalence
from the original pulled-back arithmetic model, whose topology is defined
using all local point factors. The colimit topology and the full-adele point
topology are each final from these very stages. Thus the claim concerns the
specified comparison function and specified topologies, rather than merely
existence of an unrelated homeomorphism.

The derivation uses the actual algebra-colimit universal properties in
`AdelicFixedModelAlgebraColimitStatement`, the published
`FilteredRingPointComparison`, and the final-topology construction
`ringPointColimitHomeomorph`. Local finite type is retained separately from
local finite presentation: only equality descent needs the former. The
broader arbitrary-curve-field scope is valid at this locally finitely
presented fixed-model level. Conrad's finite-type global-field application
also uses Noetherianity of the initial integer ring; that specialization is
not asserted here for an arbitrary field extension. Generic-fiber
identification, changing-base transition coherence, independence of the
initial model and further adelic topology theorems remain separate
obligations of the whole-paper task.
