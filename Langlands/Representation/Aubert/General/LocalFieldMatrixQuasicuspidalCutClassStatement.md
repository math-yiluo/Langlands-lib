# Classes of induction after Jacquet on a quasicuspidal induction

`Langlands.Aubert.General.RationalPointFamily.GL.LocalFieldMatrixQuasicuspidalCutClassStatement`
uses a positive-rank general linear group over a nonarchimedean local
field with specified `LocalFieldData`. The inducing object on the source
Levi is smooth, of finite length and quasicuspidal. Its restrictions by
the proper standard refinement radicals vanish.

Take the exact class \(x\) of normalized induction of this object.
Jacquet restriction to any standard target Levi followed by induction
has class \(m x\) for some natural number \(m\). The finite-length and
short-exact-sequence witnesses for the maps are conclusions.

The geometric filtration of Bernstein and Zelevinsky §2.12 supplies
the pieces. Quasicuspidality makes a piece vanish whenever its source
refinement is proper, as in §2.13. Each surviving piece induced to the
ambient group has the same class as the original induction by normalized
induction transitivity and Weyl invariance of induced classes.

- `bernstein-zelevinsky-1977-induced-i`, SHA-256
  `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`,
  §§2.3(c) and 2.12–2.13, printed pp. 446 and 448–449.
- `ban-jantzen-2016-duality`, SHA-256
  `7885375b64f6146a16d2b7807447bb913e411bf73735877aca2d62f80dd4dac4`,
  Proposition 4.1(3), printed p. 158.
