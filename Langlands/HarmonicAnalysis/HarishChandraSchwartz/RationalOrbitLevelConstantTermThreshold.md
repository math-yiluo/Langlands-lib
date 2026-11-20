# Constant-term thresholds uniform over an entire section level

`RationalOrbitLevelConstantTermThreshold` gives one threshold for the
normalized constant-term identity for all original sections at a fixed
level `H ≤ K`. Here `K` supplies the compact picture. The data specify
the standard parabolic along which the constant term is taken and a
compatible split component. The identity applies to every point of the
actual orbit and every point of the full minimal-Levi threshold region.

`rationalOrbitLevelConstantTermThreshold_of_perSection` takes a threshold
for each section, a finite discrete-series self-twist stabilizer, a
standard cocharacter for the output parabolic, and a `CompactOpenNormalBasis K₀ B`
whose members each satisfy `StandardParabolicBasisMember` for the
specified split component. The supplied basis subgroup is `K₀`.

On a compact fiber, the difference between the coefficient and the half
modulus times its constant term is a linear functional. The cocharacter
and basis data give the fiberwise constant-term identity that identifies
this functional on compact restrictions with the original coefficient
defect. Using the finite self-twist stabilizer, the proof finds finitely
many smooth test sections that realize each basis vector of the fixed
compact space at every parameter.
Monotonicity of the threshold regions lets the proof use a single larger
threshold for all test sections. The defect then vanishes on a basis,
hence on the entire fixed fiber. Surjectivity of the unitary parameter map
gives the identity at every original orbit point.

This is a derived fixed-level strengthening of the threshold used in
Waldspurger VI.3.1.
