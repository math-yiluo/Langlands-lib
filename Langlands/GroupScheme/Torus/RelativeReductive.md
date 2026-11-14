# Reductivity of relative tori over an arbitrary base

`RelativeTorusReductiveStatement` says that every relative torus over every
scheme `S` is a reductive group scheme, in every universe. Here a relative
torus is the actual group scheme which becomes a finite split torus on an
étale cover of `S`; its rank may vary between cover members.
`relativeTorusReductive` proves this statement, and
`RelativeTorus.IsTorus.isReductive` gives the implication for a supplied torus.
No field, connected-base or global splitting hypothesis is added.

This is an internal consequence of the existing split-torus geometry,
faithfully flat descent, the comparison between relative and field tori, and
connected reductivity of a field torus. It is a prerequisite for applying the
fibrewise central-isogeny criterion to a product with a central torus in
Task 6385. It does not establish central-torus existence or the multiplication
isogeny in that task.

The implemented proof has three parts.

1. `RelativeTorus.IsTorus.isAffineHom` uses the étale splitting cover as an
   fppf cover. Each pulled-back structure morphism is affine because it is a
   split torus. The published affine fpqc descent instance, Mathlib's
   fpqc-to-fppf descent bridge and the fppf locality theorem descend
   affineness to the original structure morphism.
2. `RelativeTorus.IsTorus.isConnectedReductive` uses the comparison
   `RelativeTorus.IsTorus.isTorus` over a field. The resulting field torus
   is connected reductive by splitting over a field extension and reflecting
   connected reductivity.
3. `RelativeTorus.IsTorus.isReductive` combines the existing smoothness of a
   relative torus with the descended affineness. Every actual geometric fibre
   is again a relative torus by arbitrary base change. Part 2 makes that
   fibre connected reductive, and the published implication to
   pseudo-reductivity supplies precisely the geometric-fibre field required
   by the definition of `IsReductive`.

All conclusions concern the supplied group scheme and its actual pullbacks.
The proof does not replace its fibres or its group law by abstract models.
