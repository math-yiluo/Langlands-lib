# Inverse right translation on the actual left quotient

Worker 112 constructs a left action of `Q` on `Induction.LeftQuotient P` by
`q • P g = P g q^-1`. The group action laws follow from the quotient's existing
right translation maps. The orbit of `P w^-1` is exactly the already published
`cosetOrbit P Q w`: inversion is a bijection of `Q`.

Joint continuity descends multiplication and inversion along the open quotient
map `G → P \\ G`, using the published left-quotient topology API. This is an
internal construction for the orbit-ordering task. It changes no existing
quotient, representative convention, target statement, or import.
