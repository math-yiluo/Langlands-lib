# Joining and composing specified original framed comparisons

This internal construction closes the composition step for actual original
framed comparisons. It uses the implemented refinement and reduced-square
calculus together with the exact quotient/join equation in
`SpecialAtlasComparisonJoin`. It is derived infrastructure for the formal-module
moduli construction; it asserts no new source theorem or representability.

`FramingSquare.join` starts with two specified comparisons of original target
atlases, an equality of their middle finer covers, and the actual quotient
framing square for each comparison. Quotient reduction preserves the specified
join as an equality of complete formal comparison records. Rewriting by this
equality identifies the desired square with the existing joined reduced
square, including the actual middle source transition. The residue-map equality
is the composite of the two given equalities, so the extended-frame map is
the identity comparison determined by that equality.

`FramingSquare.trans` handles arbitrary finer covers. It further refines the two
specified original comparisons using the actual `commonLeft` and `commonRight`
product covers, applies the proved original refinement theorem, and joins on
the equal resulting middle covers. It proves the framing condition for exactly
`c.trans d`, rather than replacing the supplied comparisons with an unrelated
witness of equivalence.

`Comparison.join` and `Comparison.trans` package these proofs with the specified
actual original target comparison and the composed residue equality. The four
projection equations are definitional. The two family-action equations show
that these constructed comparisons act by composition on every complete target
family over every coefficient test algebra. They use the underlying actual
order-linear comparison equations; point evaluations are not used to infer
equality of formal maps.

The parameters retain the nonarchimedean local field `K`, its finite-dimensional
central division algebra `D`, the supplied field `L` and its embedding into `D`,
the coefficient ring `R`, a residue field `κ`, a fixed height-certified frame
`Φ`, and one Nilp object `A : Nilp.{v,u} R (algebraMap 𝒪[K] R π)`. Original
covers may differ, finer covers may be infinite, and the quotient scalar map may
merge generators. No new target or frame is chosen. Finite-chain collapse,
varying-base framed extension and its height preservation, group actions,
polarizations, descent, levels and representability remain separate.
