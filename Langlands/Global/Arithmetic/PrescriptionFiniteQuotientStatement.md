# Finite idele-class quotients for local prescription

Author: Worker 53.

This module gives the local-product maps and states the arithmetic finite-quotient
input to finite-order Hecke-character prescription. It does not prove the
arithmetic existence assertion.

`PrescriptionLocalProduct K S` is the product of the units of the entire existing
infinite adele ring and the multiplicative groups of the actual finite completions
at the finite set `S`. The carrier universe of the number field is arbitrary.
The infinite factor retains every real sign component.

`prescriptionIdeleInclusion` inserts the whole infinite factor using the existing
`infiniteIdelesInclusion`, then multiplies the single-place finite inclusions.
It is continuous because it is a finite product of continuous maps from the
product topology to the actual idele topology. Its multiplicativity uses the
commutativity of the actual idele group. `prescriptionClassMap` composes this map
with the existing continuous quotient map. No algebraic injectivity or topological
embedding is assumed by these definitions.

`prescriptionLocalCharacter` similarly multiplies the prescribed finite characters
and the whole prescribed infinite character. The six evaluation lemmas prove
that both maps and the character restrict to exactly the existing maps and
characters on the indicated factors. The finite-factor evaluations reduce the
finite product to its sole nonidentity term.

`PrescriptionFiniteQuotientStatement` quantifies over every positive `n` and
every open subgroup `U` of this local product with finite index and containing
all `n`th powers. It asks for an open subgroup `N` of the actual idele-class group
with finite index, containing all `(2*n)`th powers, whose preimage under the
actual local-product map is exactly `U`. In particular, this is a finite quotient
of exponent dividing `2*n` with the prescribed kernel on the local factors.
It neither assumes a global character extension nor asserts a smaller period.

The original source is Artin and Tate, *Class Field Theory*, AMS Chelsea edition
(2009), Chapter X, Section 2, Theorem 4, printed p.79 (one-based PDF p.88), read
with Lemmas 2--7 on pp.77--79 and the character-extension construction on p.80.
Registered source: `artin-tate-2009-class-field-theory`, SHA-256
`af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`,
retained at `/home/taskhub/central-library/Artin-Tate--Class Field Theory--2009.pdf`.
Worker 53 read these passages directly and visually checked Theorems 4--5.
The retained appended errata (one-based PDF p.202, dated 23 January 2009) were
also read; they list no correction to Chapter X, Section 2.

The source writes `P` for the image of the selected local factors in the
idele-class group and distinguishes its induced topology from the product
topology. Here `U` lives on the product domain, so the preimage equality spells
out the restriction without identifying these topologies. Theorem 3 on p.78
provides the correspondence of open finite-index subgroups in the source route.
Including all infinite places among the prescribed places gives the whole
infinite factor used here. Theorem 4 gives exponent `m` or `2*m`, with `m` the
local quotient exponent; its proof directly gives exponent dividing `2*n`
whenever `n` kills the local quotient. This is the stated derived formulation.
Its proof remains a substantial arithmetic and topological obligation.

The actual maps and their elementary continuity and component identities are
internal constructions using the existing `Langlands.Global.Adelic` objects.
The statement is a `Prop`-valued definition. No class-field-theory package,
global character, Grunwald--Wang theorem or arithmetic existence instance is
installed by this module.
