# Recovering the weak constant term pairing from the packet pairing formula

`WavePacketWeakConstantTermPairingFormulaStatement` describes the pairing of a wave packet
with a log-square-integrable automorphic form as a functional of its spectral coefficient.
The functional uses the germs at finitely many points of the imaginary parameter space
of the standard parabolic. The formula includes the integrability of both the wave packet
pairing and the weak constant term pairing. The Eisenstein family is a fixed meromorphic
continuation of the series of the inducing form `φ`, with an open domain of holomorphy
containing all imaginary parameters. The inducing form belongs to `A²_P` for the same
compact subgroup as the packets.

The source is P. Delorme, *On the spectral theorem of Langlands*, Advances in Mathematics
426 (2023), 109107, registered as `delorme-2023-spectral-theorem-langlands`.
The PDF `Delorme--On the spectral theorem of Langlands--2023.pdf` has SHA-256
`9b2e82af72ac45c9745357d475153d43d29ec3e1ea68bf51980acf466110e2df`.
The integrability of the Levi pairing is from §3.4, (3.7), p. 15. The Fourier convention
and the differential operators are in (7.10)–(7.12), p. 25. The distribution identity
is Proposition 7.8, p. 33. Central Fourier inversion and the passage to the limit are
on p. 35. The formula is the resulting test-function identity in full imaginary
coordinates.

The proposition uses every compact subgroup in `WavePacketWeakConstantTermOrthogonalityStatement`.
Delorme's setup uses a maximal compact in good position relative to the minimal Levi.
An application of the source formula in the wider setting needs a comparison of the
inducing forms, packets, and Levi pairing measures across the change of compact subgroup.

Write \(B(X)=p_P(\varphi,\Phi_P^w)(X)\) for the pairing normalized by
\(e^{-2\rho_P(X)}\). Its summands are \(e^{-\mu(X)}p_\mu(X)\), where
\(p_\mu=p_P(\varphi,\Phi_{P,0,\mu})\). The exponent is negative because (3.7)
conjugates the weak constant term. In real relative spectral coordinates \(t\),
(7.10) uses the kernel \(e^{it\cdot X}\), so (7.11) takes the coordinate operator
to be \(D_j=i^{-1}\partial/\partial t_j\). The surviving cone in the proof of
Lemma 7.11 gives the Fourier transform of the full relative space. The derivative
in Proposition 7.8 therefore gives \(p_\mu^0(D)\delta_{\mu|_{\mathfrak a_P^G}}\).
In complex-linear distribution pairing its action on a test \(a\) is
\((p_\mu^0(-D)a)(\mu|_{\mathfrak a_P^G})\). This follows by moving each
distributional derivative onto \(a\), which contributes one minus sign.
The display in Lemma 7.11 as printed applies \(p_\mu^0(D)\) directly to \(a\)
and omits this transpose. For the symbol \(p_\mu^0(X)=1+X_1\), that display
would give the polynomial factor \(1-X_1\) on the negative Fourier phase.

Fourier inversion in the central coordinates evaluates the test at the unitary
central character of \(\Phi\). For a smooth compactly supported coefficient this
leaves such a coefficient on the relative slice, to which the norm-one formula
applies. The unitary central character of the weak constant term gives the same
central factor in \(B\). Thus the relative differential evaluations, taken on
this slice, use only the germs at finitely many full spectral points.
The constant \(C\) accounts for the nonzero scaling of the quotient and spectral
Haar measures.

`weakPairingFourierPhase e x` is
\(z \mapsto \exp(-i\langle e(z),H_P(x)\rangle)\).
On this phase, \(-D_j\) contributes the \(j\)-th relative coordinate of \(H_P(x)\).
The evaluations \(p_\mu^0(-D)\) therefore recover the relative polynomial
and the evaluation at the full spectral point recovers \(e^{-\mu(H_P(x))}\).
Their sum gives \(B(H_P(x))\). The factor
`parameterPower F P (modulusParameter F P) x` restores the unnormalized pairing
of `IsSquareIntegrableOrthogonal`.

`wavePacketWeakConstantTermOrthogonality_of_pairingFormula` proves the implication
from this formula to `WavePacketWeakConstantTermOrthogonalityStatement`. For each
split-component point, smoothness of its Fourier phase follows by writing it as
the complex exponential of a real-linear map on finite-dimensional coordinates.
Multiplying by a smooth bump that equals one on a neighborhood of the finite
frequency set gives a compactly supported smooth coefficient with the same germs
there. The standard parabolic presentation and the continuation of the series of
`φ` give a one-term `IsWavePacket` witness for the resulting packet. Complex conjugation of
its orthogonality equation, using `integral_conj`, gives the vanishing in the
orientation of Lemma 7.11. Cancellation of \(C\) makes the functional vanish on
the test and hence on the phase. The second identity of the formula then gives
the vanishing of the unnormalized pairing, and its accompanying integrability
conclusion supplies absolute convergence.
