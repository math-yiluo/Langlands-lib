# Pro-`p` radical preimages in smooth local integral models

`Langlands.BruhatTits.IntegralModels.LocalFieldPositiveProPStatement.{u}`
is a proposition target at an arbitrary universe `u`. It isolates a model
and finite-residue-field input for corrected KP Proposition 13.5.2. This
module states the target and supplies no proof.

For every nonarchimedean local field `F`, every affine, locally finite type
`F`-group scheme `G`, and supplied `D : RelativeComponentModelData 𝒪[F] F G`,
let `Q : SpecialFibreQuotientData D` satisfy `Q.IsReductiveQuotient`. The
statement says that `Q.positivePoints` is pro-`p`, with
`p = ringChar 𝓀[F]`, in the canonical point topology of `G(F)`.

The data `D` already includes smooth affine finite type full and neutral
integral models and connected fibres for the neutral model. The quotient
condition says that the specified radical is the unipotent radical of the
neutral special fibre and that the specified quotient is its represented
fppf quotient and is connected reductive. The subgroup in the conclusion is
the image in `G(F)` of neutral integral sections whose reduction belongs to
the residue-field points of this radical. No building, root datum,
Moy–Prasad filtration or Bruhat–Tits availability is assumed.

The meaning of pro-`p` is the published
`Langlands.Cohomology.IsProPSubgroup`: the residue characteristic is prime,
the subgroup is compact and totally disconnected with its subspace
topology, and every quotient by an open normal subgroup is a `p`-group.
Openness is already a separate published theorem,
`SpecialFibreQuotientData.localField_isOpen_positivePoints`, and is not an
additional conclusion of this statement.

The expected argument uses the actual congruence tower of the neutral
integral model. Its reduction kernel is pro-`p`; the residue points of the
smooth connected unipotent radical form a finite `p`-group. The radical
preimage is an extension of the image in that finite group by the reduction
kernel. Compactness and total disconnectedness use the point topology.
This describes a proof route, not established results of this module.

The statement is a derived prerequisite. KP Proposition 13.5.2 and its
proof, printed pp.476–477 / PDF pp.507–508, apply the pro-`p` property to
parahoric radicals. Here the local integral-model step is isolated from
the building assumptions, using the actual radical preimage of KP Axiom
4.1.22(7), printed p.164 / PDF p.195, and the reduction-kernel identification
in KP 13.2.6, printed p.470 / PDF p.501. It is not a transcription of a
separately numbered general-model proposition in KP.

Source: Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023), source ID
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`, at the
locations above. The internal generalization to supplied smooth integral
models is explicit; it asserts no existence of such models.
