# Canonical pushforward tensor associativity

`Langlands.Scheme.Modules.PushforwardTensorAssociativityStatement` states
associativity for the existing canonical pushforward tensor maps. It quantifies
over all schemes `X,Y : Scheme.{u}`, morphisms `f : X ⟶ Y`, and module
sheaves `M,N,P : X.Modules`, in arbitrary universe `u`, without additional
hypotheses.

Write `G` for `Scheme.Modules.pushforward f`, `T` for `tensorObj`, `t` for
`tensorMap`, `c(M,N)` for `pushforwardTensorApp f M N`, and `A` for the
fixed `tensorAssociator` from `TensorCoherenceMaps`. The proposition is

```text
t(c(M,N),id GP) ≫ c(T(M,N),P) ≫ G.map A(M,N,P).hom
  = A(GM,GN,GP).hom ≫ t(id GM,c(N,P)) ≫ c(M,T(N,P)).
```

Both composites go from `T(T(GM,GN),GP)` to `G(T(M,T(N,P)))`.
The maps `c` are the sheafification adjoints of the canonical presheaf maps
sending a pure tensor of sections to its image under the sheafification unit.
The associator `A` is the published transport of the localized monoidal
associator through `localizedTensorIso`. No maps or associativity laws are
assumed as parameters. In particular this statement assumes neither a monoidal
structure on pullback nor invertibility of its tensor comparisons.

This is an internal categorical specification authored by Worker 367, derived
from the fixed constructions in `PullbackTensor` and `TensorCoherenceMaps`.
It expresses the usual associativity diagram for a lax tensor comparison in
the explicit sheafified tensor convention. The module does not prove it or
assert a full lax monoidal structure, since unit laws are separate. Its intended
use is to transfer this equation through the existing pullback–pushforward
adjunction to prove `ExplicitPullbackTensorAssociativityStatement`.
