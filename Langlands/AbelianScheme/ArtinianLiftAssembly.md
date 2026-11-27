# Assembling a smooth proper lift from lifted transition maps

Module `Langlands.AbelianScheme.ArtinianLiftAssembly` (namespace
`Langlands.AbelianScheme.ArtinianConstantCharts.Setting`).

In the setting of `ArtinianConstantCharts`, let `K` be a family of charts of an abelian scheme `B`
over `Spec R`, and write `V U` for the open of the constant abelian scheme `C` over `Spec R'` lying
over the special fibre of `U`, so that `VT U` is its base change (`VT_eq`).

`Charts.LiftedTransitions` consists of maps `θ i j : V (U i) ⊓ V (U j) ⟶ C` over `Spec R'` that fix
points, are the inclusions on the diagonal, satisfy the cocycle condition, and whose base change to
`Spec R` is the transition map `θS i j` of the charts.

`LiftedTransitions.exists_smoothLift`: given such maps, with `R'` Artinian and `R` local Artinian
(the hypotheses of this section), there are a scheme `X`, a smooth proper morphism
`p : X ⟶ Spec R'` with a section `s`, and an isomorphism `e₀ : B ≅ X ×_{R'} Spec R` over
`Spec R` sending the unit section of `B` to the base change of `s`.

## Proof

The lifted transition maps form a gluing datum on `C` (`data`) over `Spec R'` (`isOver`). Its
base change along the closed immersion `t` has the transition maps `θS` (`θT_eq`), so the charts
`κ i` recognize `B` as the base change of the glued scheme (`TwistedOpenGluing.Data.liftIso`,
with `hcov`, `hpre`, `hκ`). The glued scheme is smooth over `Spec R'` because it is locally `C`,
and proper because its base change `B` is proper and `t` is a surjective closed immersion
(`Data.isProper_toBase`). The unit section of `B` lifts to a section of the glued scheme by
smoothness (`exists_section_lift`), since the kernel of `φ` is nilpotent (`nilpotent_ker_φ`).

## Provenance

SGA 1, Exposé III, §6 (recomposed edition, arXiv math/0206203v2, printed pp. 65–66, PDF
pp. 81–82): if the transition isomorphisms satisfy the gluing condition (1), the local lifts glue to
a lift of the scheme. In Kai-Wen Lan, *Arithmetic compactifications of PEL-type Shimura
varieties*, Harvard thesis revised 14 March 2021, a lift of a smooth scheme in the sense of
Definition 2.1.2.1 (printed p. 114, PDF p. 142) is a smooth scheme over the thicker base with an
isomorphism from its reduction to the given scheme, and the sufficiency part of the proof of
Proposition 2.1.2.2 glues local lifts in this way; this is the gluing step of the proof of
Proposition 2.2.4.1 (printed pp. 152–154, PDF pp. 180–182). `exists_smoothLift` produces such a
lift of `B`, with the isomorphism written in the direction `B ≅ X ×_{R'} Spec R`, together with
properness and a section lifting the unit section, as in Lan's Proposition 2.2.2.3 (printed
pp. 144–145, PDF pp. 172–173).
