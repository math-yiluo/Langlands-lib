# Relative tori over strictly Henselian local rings are split

This is an internal derivation from published Library results. It is a helper for the
proof of `Langlands.Geometry.Building.SpecialTorusExistenceStatement` (Kaletha–Prasad,
Proposition 9.3.4), where it shows that a torus over the integers of the maximal unramified
extension is split. The fact itself is standard (SGA 3, Exp. X), but no literature statement is
formalized here.

Let `R` be a Henselian local ring whose residue field is separably closed.

`exists_section_of_etale_of_isSepClosed`: an étale morphism `p : U ⟶ Spec R` whose image contains
the closed point has a section `σ` with `σ ≫ p = 𝟙`. The proof forms the fibre of `p` over the
residue field `κ` of the closed point. This fibre is étale over `Spec κ` and nonempty
(`Scheme.Pullback.exists_preimage_pullback`). The Library lemma
`GaloisChartPoint.exists_separable_point` gives it a point with values in a finite separable
extension `L` of `κ`. Since `κ` is separably closed (`isSepClosed_residueField_closedPoint`),
`IsSepClosed.lift` gives a `κ`-algebra map `L → κ`. Composing yields a `κ`-point of `U` over the
closed point, and `HenselianSections.exists_section_of_etale` lifts it to a section.

`RelativeTorus.IsTorus.isSplitTorus_of_isSepClosed`: every relative torus `G` over `Spec R`
(`RelativeTorus.IsTorus G`, i.e. split on the members of an étale cover) is split
(`IsSplitTorus G`). Take the cover member through the closed point and a section `σ` of it as
above. The base change of `G` to that member is split, hence so is its base change along `σ`.
That base change is isomorphic to `G` by `sectionPullbackIso`.
