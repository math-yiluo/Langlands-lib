# Reduction of the affine quotient theorem to exact-kernel representations

Worker 239, task `1cda9f1e` (affineness of a represented fpqc quotient of an
affine algebraic group). This module states one proposition,
`Langlands.GroupScheme.AffineQuotient.SmoothNormalKernelInput.{u}`, and proves
that it implies the target statement
`Langlands.GroupScheme.AffineGroupSchemeQuotientStatement.{u}`. It does not
prove `SmoothNormalKernelInput`.

## The input statement

`SmoothNormalKernelInput.{u}` says the following. Let `k : Type u` be an
algebraically closed field. Let `G` be an actual group scheme over
`Spec (CommRingCat.of k)` whose structure map is locally of finite type, affine
and smooth, so `G` is a smooth affine algebraic group. Let `i : H ⟶ G` be a
homomorphism of group schemes whose scheme map is a closed immersion
(`IsClosedSubgroup i`) and whose range is normal on every relative scheme test.
Then there are `n : ℕ` and a homomorphism `ρ : G ⟶ GL (Fin n)`
(`MatrixRepresentation G (Fin n)`) such that the range of the kernel inclusion
`kernelι ρ` equals the range of `i` as subgroup functors. The equality is
checked on points over every scheme over `Spec k`. It therefore says that the
scheme-theoretic kernel of `ρ` is the subgroup `H`, including its
infinitesimal structure, and not only that the two have the same field-valued
points. The integer `n` may be zero.

Source: J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite
Type over a Field* (2017), Lemma 5.17, printed page 103 (PDF page 119):
over an algebraically closed field, every normal algebraic subgroup of an
affine algebraic group is the kernel of a representation. The statement here
is that lemma with the extra hypothesis that `G` is smooth. Milne's algebraic
groups are group schemes of finite type over the field; an algebraic subgroup
is a closed subgroup scheme, and normality is normality of `N(R)` in `G(R)`
for every `k`-algebra `R`. The Lean wording follows Worker 706's statement
`Langlands.GroupScheme.MatrixRepresentation.NormalKernelStatement` (Milne,
Corollary 5.19, same page) word for word, except that the field is
algebraically closed and `G` is smooth. The input is chosen this way because
the reduction below only needs smooth groups over algebraically closed fields,
and these hypotheses make the input easier to prove.

## The reduction

`affineGroupSchemeQuotient_of_smoothNormalKernel` proves
`SmoothNormalKernelInput.{u} → AffineGroupSchemeQuotientStatement.{u}`. Milne
proves Proposition 5.18 (printed page 103) by taking a representation with
kernel `N` over a finite extension, applying Weil restriction, and factoring
the result through its image. The implemented proof instead first passes to the
algebraic closure and to reduced subgroups, then compares `Q` with the image
of a representation. The proof has three steps.

### Kernel lemmas

For homomorphisms of group schemes over any base:

- The imported `HopfPrimitive.isNormal_range_kernelι`: the kernel of a homomorphism is normal.
- `kernelι_comp_eq_zero`: if the kernel of `q` lies in the kernel of `f`, then
  `kernelι q ≫ f = 0`.
- `range_kernelι_le_of_comp_eq`: if `p ≫ i = f`, the kernel of `p` lies in the
  kernel of `f`.
- `range_kernelι_le_of_comp_eq_mono`: if moreover the scheme map of `i` is a
  monomorphism, the kernel of `f` lies in the kernel of `p`.

### (A) Smooth source over an algebraically closed field

`isAffineHom_of_smooth`: let `k` be algebraically closed, `G` smooth, affine
and locally of finite type, `Q` separated, and `q : G ⟶ Q` flat, surjective and
quasi-compact. Then `Q` is affine over `k`.

Proof. The kernel of `q` is a closed subgroup (`Q` is separated) and is
normal. The input gives `ρ : G ⟶ GL (Fin n)` with the same kernel. Let `I` be
the image of `ρ` (`AffineHomImage.image ρ`), a closed subgroup of `GL (Fin n)`
with projection `p : G ⟶ I` and inclusion `I ⟶ GL (Fin n)`. The image is
affine. It is smooth because `G` is smooth (`AffineHomImage.smooth_image`),
so it is reduced, and it is locally of finite type because `GL (Fin n)` is.
The projection is quasi-compact and dominant, so the published
`dominantGroupHomFlat` makes `p` flat, surjective and quasi-compact. The inclusion is a monomorphism, so the kernels of `p` and `ρ`
agree, and hence `p` and `q` have the same kernel. The published fpqc
descent of homomorphisms (`FpqcHomDescent.hom`) gives `h : Q ⟶ I` with
`q ≫ h = p` and `h' : I ⟶ Q` with `p ≫ h' = q`. Its uniqueness part shows
that `h ≫ h'` and `h' ≫ h` are identities. So the scheme map of `h` is an
isomorphism over `Spec k`, and the structure map of `Q` is that isomorphism
followed by the affine structure map of `I`.

### (B) Arbitrary source over an algebraically closed field

`isAffine_of_finite_surjective`: over any base scheme `S`, if `f : V ⟶ U`
over `S` has a finite surjective scheme map and `V` is affine, then `U` is
affine. Proof: apply the published finite-surjective affine descent for
algebraic spaces (`finiteSurjectiveAffineDescent`) to the image of `f` under
the scheme-to-algebraic-space functor. Finiteness and surjectivity pass to
that image because they are stable under base change, and `V` is represented
by an affine scheme. The resulting affine representing object is isomorphic
to `U` over `S`, since the Yoneda embedding is fully faithful.

`isAffine_of_isAffine_red`: a scheme `X` over `S` is affine once its reduced
closed subscheme `ReducedSubgroup.red X.left` is affine. Proof: the inclusion
of the reduced subscheme is a surjective closed immersion, hence finite and
surjective, so the previous lemma applies.

`isAffineHom_of_isAlgClosed`: let `k` be algebraically closed, `G` affine and
locally of finite type, `Q` separated and locally of finite type, and
`q : G ⟶ Q` with surjective scheme map. Then `Q` is affine over `k`.
Flatness and quasi-compactness of `q` are not assumed.

Proof. Let `G_red` and `Q_red` be the reduced subgroups (`reducedSubgroup`).
Over an algebraically closed field they are smooth, and `G_red` is again
affine and locally of finite type. Let `q' : G_red ⟶ Q_red` be the lift of
`G_red ⟶ G ⟶ Q` (`ReducedSubgroup.liftHom`). The inclusions of reduced
subschemes are bijective on points, so `q'` is surjective, hence dominant.
`Q_red` is reduced and locally of finite type, so `dominantGroupHomFlat`
makes `q'` flat and quasi-compact. `Q_red` is separated, since its structure
map is a closed immersion followed by the separated structure map of `Q`.
Step (A) applied to `q'` shows that `Q_red` is affine over `k`. So the reduced
subscheme of `Q` is affine, and `isAffine_of_isAffine_red` shows that `Q` is
affine. A morphism from an affine scheme to `Spec k` is affine.

### (C) Arbitrary field

`affineGroupSchemeQuotient_of_smoothNormalKernel`: take the data of the target
statement over an arbitrary field `k` and let `b : Spec k̄ ⟶ Spec k` be the map
to the algebraic closure (`toAlgebraicClosure k`). The base changes of `G` and
`Q` along `b` (`GroupScheme.baseChange b`) keep the finiteness, affineness and
separatedness hypotheses, because these are stable under base change. The
square of `q` and its base change is a pullback square
(`DominantHomFlat.baseChange_isPullback`), so the base change of `q` is
surjective. Step (B) shows that the base change of `Q` is affine over `k̄`, so
its underlying scheme is affine. This scheme is the fibre product of
`Q.X.hom` and `b`. The published field-extension affine descent
(`fieldExtensionAffineDescent`) shows that `Q.X.left` is affine, and hence
`Q.X.hom` is affine.

Of the three hypotheses on `q` in the target statement, the proof uses only
surjectivity. It also does not use quasi-compactness of `Q`'s structure map.

## Use

Worker 706 proves `SmoothNormalKernelInput.{u}` separately. The final proof of
the task applies `affineGroupSchemeQuotient_of_smoothNormalKernel` to that
proof.

The final theorem depends only on the standard axioms `propext`,
`Classical.choice` and `Quot.sound`.
