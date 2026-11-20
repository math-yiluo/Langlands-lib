# Smooth torus moduli from the noetherian geometric inputs

`AffineFiberTorusModuliInputsStatement.{u}` lists three inputs for smooth
separated quasi-compact groups over noetherian affine schemes with affine
geometrically connected residue fibres. The inputs are affine pullbacks on
local Artinian affine tests, adic-limit bijectivity of the small presheaf of
actual closed tori, and a smooth parameter with a universal closed smooth
geometrically connected centralizer. A centralizer parameter assigns each
actual closed torus subgroup on each test to the unique parameter whose
subgroup evaluation is the centralizer of that torus.

`smoothAffineFiberTorusSubgroupRepresentability_of_moduliInputs` proves the
original arbitrary-base statement from those inputs. Base-change the ambient
group to the centralizer parameter and apply the étale fixed-centralizer
moduli theorem. The resulting parameter is smooth over the original base by
composition. Its closed torus family is universal because the centralizer of
a test torus first determines a unique point of the centralizer parameter.
The torus itself then determines a unique point of the fixed-centralizer
scheme. The actual ambient pullback comparisons preserve and reflect literal
subgroup equality. The connected and arbitrary-base reductions produce the
stated conclusion in the original universe.

This is the conditional assembly in the sufficiency direction of Raynaud,
SGA 3, Exposé XV, Theorem 8.9(a) and Corollary 8.11, Gille–Polo recomposition,
PDF pp. 62–63. The three geometric inputs are explicit premises.
