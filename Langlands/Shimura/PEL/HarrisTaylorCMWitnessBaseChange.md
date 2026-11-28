# Pullback and reflection of normalized CM witnesses

`levelDataBaseChange_witness` pulls a witness between two Harris
representatives at \(b\circ t\) back along \(b\colon T\to S\), where
\(t\) is a geometric point of \(T\). It retains the multiplier and uses the
pulled-back rational equivariant isomorphism. The proof first applies
naturality of the dual-pullback equation to the canonical pullbacks of the
polarizations. The compatibility diagram for the Weil-adelic level
equivalences then transports the orbit equality.

`levelDataBaseChange_reflect` reverses the orbit argument for a given
rational isomorphism and multiplier satisfying the polarization equation
on both bases. The same Weil-adelic diagram identifies the pulled-back
images of the original orbit equation. Injectivity of
`Tate.weilAdelicLevelBaseChange` on the pointed orbits gives the original
equation. `levelDataBaseChange_multiple_reflect` supplies the original
polarization equation when rational Hom pullback detects zero. It
specializes `IsRationalDualPullbackMultiple.integral_of_baseChange_of_naturality`
to the two actual polarizations.
