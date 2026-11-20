# A common reproducing kernel for an archimedean family

`SmoothFamily.smoothingLM` applies one actual compactly supported smooth archimedean kernel in every slice. A compact-central kernel commutes with the diagonal compact action.

Let the family's generating map be an intertwiner from a finite-dimensional compact representation, with image killed by a fixed cofinite center ideal. The action on that image is continuous, so the proof first replaces the algebraic source with a finite continuous source having the same image. Each smooth slice of a generator is compact-finite by equivariance and center-finite because its center orbit factors through the quotient. The resulting joint finiteness puts every simultaneous right translate of the generator in the closure of the generated enveloping module. The same holds for its smoothing by simultaneous averaging.

Every compact-central smoothing of the source map is therefore a compact intertwiner into this closure. The finite-dimensional bound on these intertwiners puts their values in one finite-dimensional subspace of families. Evaluating on the coordinate basis of the source and then in each slice gives a linear map from the central kernels with finite-dimensional, hence closed, range in the product of smooth spaces.

In the product topology, any neighborhood of the original basis evaluations specifies conditions in finitely many slices. The Library's simultaneous approximation theorem sends all those slices into their prescribed neighborhoods with one compact-central kernel. Hence the original basis evaluations belong to the closure of the smoothing range, and closedness yields one kernel reproducing all of them. Linearity and equality of generating images give exact reproduction for every original source vector in every slice.

This internal construction follows the reproducing-function argument in Borel–Jacquet, *Automorphic forms and automorphic representations* (1979), §§1.6 (2) and 2.1, printed pp. 191 and 193, PDF pp. 186 and 188. The family construction makes a single kernel available to the whole fixed-level multiplicity space in the finiteness argument of §4.3 (i), printed p. 195, PDF p. 190.
