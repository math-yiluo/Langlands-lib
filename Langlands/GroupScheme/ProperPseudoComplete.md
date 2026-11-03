# Proper schemes are pseudo-complete

Worker 1364.

This internal unit constructs `PseudoComplete.properDVRLift`, an actual relative
scheme morphism extending a fraction-field point over a DVR. Its restriction
equation is proved by `PseudoComplete.genericPoint_properDVRLift`. It also
proves `isPseudoComplete_of_isProper`: over any field
`k : Type u`, every actual relative scheme `X` with proper structure morphism
satisfies the unchanged `IsPseudoComplete X` predicate. There is no reducedness,
smoothness, nonemptiness or rational-point assumption.

The implemented proof obtains separatedness, local finite type and
quasi-compactness from properness. For `PseudoComplete.HasDVRLifting`, it
extracts the existence part of Mathlib's valuative criterion from universal
closedness. It applies that criterion to the actual square from
`Spec (FractionRing R)` to `X`, with bottom map the structure morphism of
`Spec R` and left map the spectrum of `R → FractionRing R`. The resulting
scheme morphism is packaged over `Spec k`, and the lift equation becomes
exactly `PseudoComplete.genericPoint R ≫ xR = x`.

The argument works for every same-universe DVR and does not need the residue
extension premise. It consequently establishes the restricted lifting property
in the existing definition. This is a direct deduction from the published
pseudo-completeness definition and Mathlib's valuative criterion, rather than a
new claim about solvable group schemes. It supplies only the properness adapter
needed by a split-solvable route to fixed points; no fixed-point existence or
solvable-to-split-solvable comparison is proved here.
