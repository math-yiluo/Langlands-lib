# Finite unramified stages of every positive degree

For a nonarchimedean local field \(F\) with residue cardinality
\(q\) and a positive integer \(n\), `finiteUnramifiedFieldOfDegree`
adjoins a primitive root of order \(q^n-1\) in the actual separable
closure. The field is finite. Its generator is fixed by inertia,
so the finite unramified criterion gives arithmetic unramifiedness.
Every Galois conjugate of the root is a power of it, which proves
normality. Separability is inherited from the ambient closure.

The residue of the root satisfies \(x^{q^n}=x\), so its residue
minimal polynomial has degree dividing \(n\). The Teichmüller
degree comparison bounds the field degree by that residue degree.
Conversely, the residue field of the constructed stage contains
a primitive root of order \(q^n-1\), so it has at least \(q^n\)
elements. Its cardinality is \(q\) to the field degree because the
stage is unramified. These bounds give degree exactly \(n\).

This construction realizes the finite-residue-field case of
Serre, *Local Fields* (1979), Chapter III, §5, Theorem 2,
printed p. 54, and the positive-degree stages used in Chapter XIII,
§§2–3. The Lean proof uses Teichmüller roots inside the chosen
separable closure in all characteristics.
