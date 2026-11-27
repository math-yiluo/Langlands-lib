# Continuous Galois evaluation on the normed unramified completion

The Krull Galois group of the actual inertia fixed field acts isometrically on its normed completion. On the embedded algebraic field, an element has an open stabilizer and its orbit map is locally constant. For an arbitrary element of the completion, approximation by an algebraic element and the isometry give continuity of the orbit map. Joint continuity follows from the triangle inequality using orbit continuity and the isometry in the field variable.

Harris, *Galois properties of cohomological automorphic forms on GL(n)*, J. Math. Kyoto Univ. 39(2) (1999), §4, p. 309, (4.3), uses \(F^{\mathrm{nr}}\) as the local base on the Shimura side. This construction gives continuous Galois evaluation on the normed completion of the unramified field. Berkovich, *Étale equivariant sheaves on \(p\)-adic analytic spaces*, §1.1.1(i), p. 2 (1996), gives the analogous motivation from a continuous Galois action on analytic base change to the completed algebraic closure.

`completedFieldMulAction` packages the same action, with continuity for the Krull topology provided by `completedFieldMulAction_continuousSMul`.
