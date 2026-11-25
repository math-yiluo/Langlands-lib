# Affineness from connected reductive residue fibres

`Langlands.GroupScheme.ReductiveFiberAffinenessStatement.{u}` is a Prop-valued
statement definition. This module does not prove it.

For every scheme `S` in universe `u` and group scheme `G` over `S`, assume
`Smooth G.X.hom`, `IsSeparated G.X.hom`, `QuasiCompact G.X.hom`, and connected
reductivity of every actual residue-field fibre
`RelativeIdentityComponent.residueFiber G s`. The conclusion is
`IsAffineHom G.X.hom`. There is no Noetherian, reducedness, connectedness or
quasi-separatedness hypothesis on the base.

Smoothness gives local finite presentation. Separatedness gives
quasi-separatedness of the morphism, and quasi-compactness supplies the remaining
part of finite presentation. The fibre hypothesis includes smoothness,
affineness and connectedness of each residue-field fibre, and triviality of its
geometric unipotent radical. It concerns the supplied group scheme itself,
without choosing an identity-component representative.

The source is M. Demazure and A. Grothendieck (eds.), *Schémas en groupes*
(SGA 3), Exposé XVI, *Groupes de rang unipotent nul*, Theorem 5.2(i), in the
Gille–Polo recomposition (2008–2009), printed p.320, original pp.524–525,
one-based PDF p.20 of `Expo16.pdf`. It is registered as
`sga3-expose-xvi-gille-polo-2009`, SHA-256
`3db23f1a2e7942fe7c63c7a4475f76c67944f8a51996241d9e40127435fb892b`.
The retained file is
`Demazure-Grothendieck--Schemas en groupes, SGA 3 (Gille-Polo edition with original text)--2011/Tome 2 - Exposes VIII-XVIII/Recomposition Gille-Polo (2008-2009)/Expo16.pdf`
under the Central-Library.

The source theorem treats a smooth finitely presented group with connected
affine fibres and one reductive fibre at a specified base point. It gives an
open neighbourhood on which the group is reductive. Here every residue-field
fibre is reductive, so these neighbourhoods cover `S`. Reductivity includes
affineness, which is local on the target, and hence gives the conclusion.
The separatedness hypothesis in the Lean statement is a permitted restriction
of the source theorem.

Brian Conrad, *Reductive group schemes* (2014), uses exactly this affineness
consequence in the proof of Proposition 3.1.3, pp.82–83. That source is registered
as `conrad-2014-reductive-group-schemes`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
Conrad explains there that finite presentation can replace affineness in the
definition of a reductive group scheme.

This focused prerequisite does not assert closedness of an identity-component
inclusion or representability of a component quotient.
