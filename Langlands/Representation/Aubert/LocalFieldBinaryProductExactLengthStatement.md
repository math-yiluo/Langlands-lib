# Finite length and separate exactness of the local-field GL product

`Langlands.Aubert.LocalFieldBinaryProductExactLengthStatement` supplies the
preservation properties for the actual normalized induction product on exact
Grothendieck groups. The field is any nonarchimedean local field supplied by
`Langlands.LocalFieldData`. The two ranks \(a,b\) range over the natural
numbers. The smooth complex representation carrier universe is
`max uF uV`, with `uF` the field universe.

For positive \(a,b\), the product takes the exterior tensor representation
on the upper-block Levi of shape \((a,b)\) and uses the positive half-modulus
normalized induction to \(\mathrm{GL}_{a+b}(F)\). At rank zero the
published binary functor tensors with the representation of the trivial
group and pulls the other action back along the rank equality. This also
covers the product of two rank-zero representations.

The first clause asserts finite length of the product when both factors
have finite length. Each remaining clause fixes a finite-length factor
and asserts injectivity, surjectivity and the image-kernel identity for the
induced maps of every actual short exact sequence of finite-length
representations in the other factor. The clauses are exactly the inputs
to `SmoothRep.FiniteLengthGrothendieckGroup.map₂`, which sends the two
actual classes to the class of their normalized product.

Zelevinsky 1980 §1.1 specifies the field, the trivial rank-zero group,
and the upper-block Levi convention. §§1.4 and 1.7 use finite-length
preservation and additivity to define the product of exact classes.
The separate exactness conditions express the tensor exactness over
\(\mathbb C\) and the exactness of the induction functor in
Bernstein–Zelevinsky 1977 §§1.8–1.9 and 2.2–2.3. Bernstein–Zelevinsky
§§2.5 and 2.8 give the irreducible embedding and finite-length cuspidal
induction inputs for finite-length preservation. At rank zero the
finite-length factors are finite-dimensional complex vector spaces,
and tensoring with one takes a finite direct sum of the other
representation.

- `zelevinsky-1980-induced-ii`, SHA-256
  `663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`,
  §§1.1, 1.4 and 1.7, printed pp. 170–173.
- `bernstein-zelevinsky-1977-induced-i`, SHA-256
  `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`,
  §§1.8–1.9, 2.2–2.3, 2.5 and 2.8, printed pp. 444–445 and 446–448.
