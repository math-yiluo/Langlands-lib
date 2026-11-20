# Supercuspidality from a common sigma-lift and a norm twist

`IsNormTrivial.isOpen_ker` applies the neighbourhood theorem for \(d\)-th powers in a complete nontrivially normed field of characteristic zero. Here \(d\) is the positive degree of the finite extension. Each such power is the norm of the corresponding base-field unit viewed upstairs. The character is trivial on a neighbourhood of the identity, so its kernel is open.

`IsNormTrivial.toSmoothCharacter` equips the original character with its open-kernel proof. The determinant pullback also has open kernel by continuity of determinant. The existing theorem `GeneralLinear.isSupercuspidal_twist_iff` then gives invariance of admissibility and vanishing of the proper Jacquet quotients.

`isSupercuspidal_of_sigmaOrbitLift_of_fibre` takes cuspidal sigma-lift existence from the \(a=1\) case of Henniart–Lemaire (2011), II.4.12, Remarque, printed p. 97, as a premise. The proved orbit-period criterion supplies its hypothesis with the period equal to the extension degree. The existence statement yields an irreducible supercuspidal action with the same actual normalized orbit product as sigma-lift.

The other premise is the norm-twist comparison of the supplied downstairs action with that supercuspidal action in the common fibre. Henniart–Lemaire (2011), II.4.8, Lemme (2), printed pp. 90–91, compares an essentially square-integrable member of a fibre with any other irreducible smooth generic member. Here the supercuspidal member is the essentially square-integrable one in that application. The implemented proof uses the supplied representation equivalence and invariance under norm-trivial determinant twist to conclude supercuspidality.
