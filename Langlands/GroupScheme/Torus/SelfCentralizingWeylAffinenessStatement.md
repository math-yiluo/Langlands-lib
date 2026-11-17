# Affineness detected by a self-centralizing torus's Weyl quotient

The proposition
`Langlands.GroupScheme.SelfCentralizingTorusWeylAffinenessStatement.{u}`
states the supplied self-centralizing maximal-torus case of SGA 3,
Exposé XVI, Theorem 4.1(d), including the existence of the normalizer and
Weyl quotient from Exposé XV, Proposition 7.1(iv).

## Hypotheses and conclusion

For an arbitrary scheme `S : Scheme.{u}`, let `G` be a group scheme whose
structure morphism is smooth, separated, and quasi-compact. Assume that
each actual residue-field group
`RelativeIdentityComponent.residueFiber G s` is connected and affine.
These hypotheses give a smooth group of finite presentation over `S`;
affineness of `G` over `S` is a conclusion to be detected.

Supply a commutative group scheme `T` and a homomorphism `t : T.toGrp ⟶ G`
with the following properties:

- `RelativeTorus.IsTorus T.toGrp`: the group becomes a finite split torus
  on an étale cover of `S`, with rank allowed to vary between cover members.
- `IsClosedSubgroup t`: the underlying scheme map is a closed immersion.
- `IsFibrewiseMaximalTorus t`: the actual torus inclusion on every
  residue-field fibre is a maximal torus.
- `(torusCentralizer t).IsRepresentedBy t`: the given inclusion represents
  its full centralizer functor. In particular, after every refinement of
  every test scheme, a point centralizing every torus point comes from `T`.

The conclusion supplies group schemes `N`, `W`, homomorphisms
`n : N ⟶ G`, `q : N ⟶ W`, and these properties:

1. `n` is a closed subgroup inclusion representing the actual
   `torusNormalizer t` functor, and `N` is smooth over `S`.
2. `W` is separated, quasi-compact, and étale over `S`.
3. The scheme map underlying `q` is flat, surjective, and locally of finite
   presentation.
4. For every `U : Over S` and `y : U ⟶ N.X`, `y` maps to the identity in
   `W(U)` if and only if its image in `G(U)` lies in the image of `T(U)`.
5. `IsAffineHom G.X.hom ↔ IsAffineHom W.X.hom`.

The normalizer is tested after every refinement, as in the imported
`torusNormalizer` definition. The fppf map and its kernel condition describe
the actual quotient sheaf `N/T`: they do not assert that the naive quotient
`N(U)/T(U)` is `W(U)` for each test scheme. The map `T ⟶ N` is determined by
the representing normalizer and its inclusion in `G`.

## Source correspondence and derived formulation

The primary source is M. Demazure and A. Grothendieck (eds.), *Schémas en
groupes* (SGA 3), Exposé XVI, *Groupes de rang unipotent nul*, Gille–Polo
recomposition (2008–2009), Theorem 4.1(c)–(d), printed pp.318–319
(original pp.519–521), one-based PDF pp.18–19 of `Expo16.pdf`.
Registered source: `sga3-expose-xvi-gille-polo-2009`, SHA-256
`3db23f1a2e7942fe7c63c7a4475f76c67944f8a51996241d9e40127435fb892b`.

The source assumes connected affine fibres of unipotent rank zero and
states the equivalence of affineness of `G`, its central quotient, its
maximal-torus normalizer, and `N/T`. This proposition selects the
equivalence between `G` and `N/T` and supplies an actual self-centralizing
maximal torus. On each geometric fibre the centralizer of that maximal
torus is the torus itself, so its Cartan subgroup has unipotent rank zero.
This is the supplied-torus formulation of the source's rank hypothesis;
it does not assume that the whole geometric fibre is reductive. Passing
from the all-test-scheme centralizer hypothesis to the geometric fibres,
and identifying their rank, remain proof obligations.

The supporting source is M. Raynaud, SGA 3, Exposé XV, *Compléments sur les
sous-tores d'un préschéma en groupes. Application aux groupes lisses*,
Gille–Polo recomposition (1 December 2008), Definition 6.1 ter, printed
p.271 (original p.423), one-based PDF p.39, and Proposition 7.1(iv),
printed p.282 (original p.446), one-based PDF p.50 of `Expo15.pdf`.
Registered source: `sga3-expose-xv-raynaud-2008`, SHA-256
`03647e0232067a7508bb1350e7aace3e88d58872956f068ced808a4f9cc3273f`.
Proposition 7.1 applies to a smooth group of finite presentation with
connected fibres and a smooth subgroup whose fibres are torus
centralizers. It gives the smooth closed normalizer and the separated
étale quotient of finite type used here.

The declaration is a `Prop`-valued definition. It records an unproved
structural prerequisite for fibrewise affineness. It does not include
the other conclusions of XVI 4.1, such as quasi-affineness, affineness
over bases of dimension at most one, or the central-quotient criterion.
There is no assertion here that `W` is finite over an arbitrary base.
