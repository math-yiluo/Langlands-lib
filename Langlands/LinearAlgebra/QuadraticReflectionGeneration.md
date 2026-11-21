# Generation of regular quadratic isometries by reflections

`reflectionWord` applies a list of reflections in order. Each vector in the list has nonzero quadratic value. Over a field with `2` invertible, an isometry of a finite-dimensional form with nondegenerate polar pairing is represented by a reflection word.

An orthogonal basis has nonzero values on its basis vectors. The proof matches the basis to its isometric image one vector at a time. To match two vectors of equal nonzero value, reflect in their difference if it has nonzero value. Otherwise reflect in their sum and then in the target vector. Both constructions fix every vector orthogonal to the pair. They therefore preserve all the previously matched basis vectors.

The determinant of a reflection is minus one because it is minus the identity on its line and the identity on the orthogonal complement. Consequently the determinant of a word is `(-1)` to the length of the word, and a determinant-one isometry has an even reflection expression. This is the reflection generation statement of Cartan and Dieudonné. The proof is derived from the Library's quadratic Witt extension and the reflection construction used for the quadratic spin case in Kneser, *Lectures on Galois Cohomology of Classical Groups*, §5.9, pp. 93–94 (PDF pp. 99–100).
