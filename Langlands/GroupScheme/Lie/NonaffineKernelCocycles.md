# Actual square-zero kernel cocycles

Work in `Langlands.GroupScheme.Lie.NonaffineKernel`. Let `G` be any group scheme over a commutative ring `R`, let `A` be an `R`-algebra, and let `J` be a square-zero ideal of `A`, expressed by `Fact (SmoothLifting.SqZero J)`. The module uses the actual reduction kernel `kernel G J` and its existing additive `A`-module structure. The target group scheme is not assumed affine, separated or smooth. The point group `P` is arbitrary in the same universe.

Suppose a function `s : P → G(A)` reduces to a supplied homomorphism `s₀ : P → G(A/J)`. `reductionLiftAction` sends `h` to linear conjugation by the actual point `s(h)` on `Additive(kernel G J)`. This is a group homomorphism into linear automorphisms: conjugation depends only on the reducing acting point, so the identity and multiplication laws follow from those for `s₀`. The point formula is exactly `x ↦ s(h) x s(h)⁻¹`, regardless of whether `s` itself is a homomorphism.

`kernelDefect` is the actual kernel element with underlying point `s(h) s(k) s(hk)⁻¹`. Membership follows by reducing this expression through `s₀`. Associativity proves its additive two-cocycle equation:

`d(h,k) + d(hk,l) = h • d(k,l) + d(h,kl)`,

where the action is `reductionLiftAction`. The proof evaluates both sides in the actual group and uses cancellation. `kernelDefect_correctionEquation` translates an additive coboundary equation `d(h,k) + b(hk) = h • b(k) + b(h)` into exactly the ambient group-valued correction equation for `b⁻¹ s`.

For actual homomorphisms `f,f' : P → G(A)` with equal reductions, `kernelDifference` has underlying point `f'(h) f(h)⁻¹`. It satisfies the additive one-cocycle equation for conjugation through `f`. If an actual kernel module element `m` is a one-coboundary primitive, `kernelDifference_conjugacy` proves

`f'(h) = m⁻¹ f(h) m`.

Here the points denoted by `m` and `m⁻¹` are the actual kernel points underlying the additive module element. The proof rewrites `action(h)(m) - m` as `-m + action(h)(m)`, using the commutativity of the square-zero kernel, and then cancels in the ambient group. This fixes the sign of the conjugating element.

The naturality lemmas use the actual kernel coefficient map from `NonaffineKernelMap`. Given `q : A →ₐ[R] B` and `J.map q ≤ J'`, underlying point values commute with this map. If both ideals are square-zero, coefficient change intertwines the linear conjugation automorphisms and the actions of compatible reducing lifts. Defects and differences of compatible maps also commute with coefficient change; these last point-valued identities do not require square-zero ideals. The proofs apply the underlying point map and its multiplication and inversion laws.

This is internal derived deformation algebra. Worker 496's unchanged supporting pairs construct the actual nonaffine kernel module and semilinear coefficient maps; the present module applies elementary group identities to those constructions. It neither constructs a scheme lift, identifies these kernels with scalar extensions on arbitrary tests, nor constructs regular cochains or proves their vanishing. Those geometric steps and the full homomorphism lifting statement remain separate obligations.
