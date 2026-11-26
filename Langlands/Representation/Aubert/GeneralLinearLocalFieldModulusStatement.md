# The full upper-block modulus over a nonarchimedean local field

`Langlands.Parabolic.LocalFieldGeneralLinearModulusCompatibilityStatement`
identifies the two positive characters on the entire upper block parabolic
of \(\mathrm{GL}_n(F)\). The first is the Haar module for conjugation on the
actual closed unipotent radical \(U_B\). The second is the character
\(\delta_B\circ\pi_B\), where \(\pi_B\) is the diagonal-block projection
and

\[
\delta_B(m)=\prod_{i<j}|\det m_i|_F^{n_j}\,|\det m_j|_F^{-n_i}.
\]

The absolute value is normalized by the residue cardinality. For \(g\) in
the parabolic, write \(c_g(u)=gug^{-1}\). The Haar-module convention asserts
\((c_g)_*\mu=\delta_B(\pi_B(g))^{-1}\mu\) for a Haar measure \(\mu\) on \(U_B\).
The equality on the full parabolic identifies the scalar used on every
element of the inducing covariance group. Restriction to the Levi also
identifies the scalar whose inverse positive square root defines the
normalized Jacquet action.

The field and topology are the actual data of `LocalFieldData F`, including
positive characteristic. Every ordered block shape \(B\) is included. At rank
zero the parabolic, Levi and radical are trivial, and the empty product is
one.

The statement is a specialization of the Haar-module definition and
normalized functor conventions in Bernstein and Zelevinsky 1977 §§1.7–1.8,
printed p. 444, and the standard upper-block triple of §§2.1–2.3,
printed p. 446. Its determinant factor comes from the action
\(X_{ij}\mapsto m_i X_{ij}m_j^{-1}\) on the strictly upper-block entries.
The equality on the full parabolic follows mathematically from this Levi
computation, the triviality of the inner Haar module on the unipotent
radical, and the Levi decomposition.

- `bernstein-zelevinsky-1977-induced-i`,
  SHA-256 `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`,
  §§1.7–1.8 and 2.1–2.3, printed pp. 444 and 446.
