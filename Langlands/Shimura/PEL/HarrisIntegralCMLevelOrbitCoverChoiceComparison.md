# Canonical comparison of equal Harris monodromy orbit-cover choices

This internal construction canonically compares the original finite Harris
covers selected by two raw classes with the same actual monodromy orbit.
The comparison preserves raw fibre evaluation and satisfies identity,
composition and inverse laws. It also identifies the original cover
point-comparison morphisms obtained from any two supplied paths, after
comparing their dependent target orbit choices by this canonical map.

The namespace is
`Langlands.Shimura.PEL.HarrisPolarizedWeilLevel`. Arithmetic carriers,
schemes and geometric-point fields have universe zero.

## Inputs and original objects

Retain the original central simple unitary datum `D`, normalized Harris
signature charts `C`, all displayed number-field and scalar structures,
and the named prerequisite package `P`. Supply an actual abelian scheme
`B/S`, a dual witness `W`, a morphism `lam : B ⟶ W.dual P`, and an
integral order action `a` on the pullback of `B` to an object `T : Over S`.
The underlying scheme of `T` is quasi-separated, connected and locally
noetherian. A full CM condition or a polarization proof for `lam` is not
an additional premise of this conditional cover comparison.

Retain the finite Weil transition statement, rational profinite-integer
and adele comparison, and torsion finite-etale statement. Every indexed
torsion order is a unit on `T.left`, and each corresponding roots-of-unity
scheme is finite and etale over it. Supply an algebraically closed field
`Ω`, a point `s : Spec Ω ⟶ T.left`, and a witness `hs` of finiteness of
all actual finite-etale fibres there.

Write `Γ_s = FundamentalGroup s hs`, and let `Raw_s(V)` be the original
right-orbit quotient of actual Harris Weil frames by
`((hodgeLevelFunctor D C).obj V).subgroup`. The original right action
uses the opposite similitude group; its commuting left monodromy action
is the original Tate action. All action instances in the Lean statements
are these actual constructions.

Fix original Harris levels `U,V` and a witness `hU` that the original
`harrisIntegralCMFullActionLevelTower` at `s,U` is nonempty. For a raw
class `q`, write `C_s(q)` for the existing
`harrisIntegralCMFiniteOrbitCover` with this reference level. Its fibre
comparison is the original equivalence

```text
E_s(q) : Fiber s (C_s(q)) ≃ Γ_s · q.
```

Here `Γ_s · q` is the subtype consisting of the actual monodromy orbit.
Write `e_s(q)(x) = (E_s(q)(x)).val` for its underlying raw class. The
private `orbitCoverRaw` is exactly this function; its injectivity follows
from injectivity of `E_s(q)` and subtype extensionality. Its equivariance
is the underlying-value consequence of the original fibre-equivariance
formula.

## Canonical comparison for equal orbits

For `q,r : Raw_s(V)` and an equality

```text
hqr : Γ_s · q = Γ_s · r,
```

`harrisIntegralCMFiniteOrbitCoverOrbitEqIso` constructs an isomorphism

```text
J_s(q,r,hqr) : C_s(q) ≅ C_s(r)
```

in the original category of finite-etale covers of `T.left`. Thus it
compares actual schemes over the same test, rather than only their
abstract orbit sets.

The private `orbitActionEqIso` sends a member of `Γ_s · q` to the same
raw value regarded as a member of `Γ_s · r`. Its inverse does the reverse.
The orbit equality supplies membership, both inverse equations are
reflexive, and equivariance follows because the raw values are unchanged.
The original `geometricContinuousActionEquivalence s hs` makes
`continuousActionFunctor s hs` an equivalence. Applying its inverse
functor to this action isomorphism gives `J_s` between the original
chosen covers. No replacement cover construction is introduced.

`harrisIntegralCMFiniteOrbitCoverOrbitEqIso_raw` proves the exact formula

```text
e_s(r)(x ≫ J_s(q,r,hqr).hom.hom) = e_s(q)(x).
```

It takes the underlying value of the original
`harrisIntegralCMFiniteOrbitCoverMap_fiber` formula for the action map
just constructed. In particular, the raw-value preservation is proved,
not supplied as an assumption at the public interface.

The following public laws use the same `U,V,hU` throughout:

- `harrisIntegralCMFiniteOrbitCoverOrbitEqIso_refl` proves
  `J_s(q,q,rfl) = Iso.refl _`.
- `harrisIntegralCMFiniteOrbitCoverOrbitEqIso_trans` proves
  `J_s(q,r,hqr) ≪≫ J_s(r,t,hrt) = J_s(q,t,hqr.trans hrt)`.
- `harrisIntegralCMFiniteOrbitCoverOrbitEqIso_symm` proves
  `J_s(q,r,hqr).symm = J_s(r,q,hqr.symm)`.

For the first two laws, isomorphism extensionality reduces to equality
of cover morphisms. The private `coverHom_ext` uses faithfulness of the
original continuous-action functor to test this on actual fibres at
`s`. Injectivity of the final fibre comparison and the raw formula then
prove the equality. The inverse law follows by cancelling the forward
isomorphism in the composition law and using the identity law.

## Independence of the supplied point path

Additionally supply an algebraically closed field `Ω'`, a point
`r : Spec Ω' ⟶ T.left`, finiteness `hr` of all its finite-etale fibres,
and two paths

```text
p,p' : fiberFunctor s hs ≅ fiberFunctor r hr.
```

Write `R_p` for the original `harrisIntegralCMWeilRawPointEquiv`. For
each raw `q`, the original
`harrisIntegralCMFullActionLevelPointNonempty` derives a nonempty
reference level at `r` from `hU`; no independent target reference level
is assumed. Write

```text
I_p(q) : C_s(q) ≅ C_r(R_p(q))
```

for the original `harrisIntegralCMFiniteOrbitCoverPointIso`. The
previously proved raw orbit path-independence theorem gives

```text
Γ_r · R_p(q) = Γ_r · R_p'(q).
```

The equality used in Lean is
`harrisIntegralCMWeilRawPointEquiv_orbit_path_independent` with arguments
`p',p`, whose orientation is exactly the one displayed. Let `J_r` be
the canonical equal-orbit comparison above using this equality.

`harrisIntegralCMFiniteOrbitCoverPointIso_path_independent` proves the
following equality of morphisms in the actual cover category:

```text
I_p(q).hom ≫ J_r(R_p(q), R_p'(q)).hom = I_p'(q).hom.
```

The two derived target reference-level witnesses are proofs of the same
nonemptiness proposition; proof irrelevance identifies their occurrences
in these dependent cover expressions. The theorem compares the target
choices explicitly and does not assert a literal equality between
isomorphisms with different displayed target objects.

The proof uses the actual target loop `g = p.symm ≪≫ p'`. The private
`path_change_apply` proves `p'(y) = g • p(y)` for every actual cover
fibre element, using the componentwise inverse law of the path. The
private `path_change_eval` applies any supplied equivariant evaluation
to that identity. For the actual Harris evaluations, equivariance, the
original point-isomorphism raw formula and the original raw path-change
formula give the private `orbitCoverPointIso_change_eval`:

```text
e_r(R_p(q))(p'(x ≫ I_p(q).hom.hom)) = R_p'(e_s(q)(x)).
```

The private `path_composition_eval` combines component naturality of
`p'` with preservation of raw evaluation by `J_r`. Its specialization
`orbitCoverPointIso_comp_eval` shows that the left side of the claimed
cover-morphism equality, after path `p'` and raw evaluation, has the value
`R_p'(e_s(q)(x))`. The original raw formula for `I_p'` gives the same
value for the right side. The private `coverHom_ext_raw` uses
injectivity of the target raw evaluation, bijectivity of the path
component and source-fibre faithfulness to conclude equality of the
actual cover morphisms. The generic calculations stay private; every
hypothesis they need is proved for the original Harris maps.

The public raw and coherence theorems and the path-independence theorem
omit the unused `IsCMField F` and `IsScalarTower ℚ F A` assumptions.

## Provenance and retained obligations

This is an internal deduction from the original Harris finite orbit
actions, selected covers, cover-map fibre formulas, actual point
comparison, actual raw path-change and orbit-independence theorems,
and the proved geometric continuous-action equivalence. It introduces
no external literature assertion or geometric existence assumption.

The result retains the supplied family, reference level and paths and
concerns connected locally noetherian tests. It does not construct paths,
compare different reference levels, glue disconnected tests, or establish
the full normalized rational-isogeny moduli comparison. Determinant/Lie
and Rosati integration, admissibility, and existence of a smooth
projective representing PEL scheme remain obligations of the host task.
The exact `DivisionCMRepresentabilityStatement` and all imported
Lean/Markdown pairs are preserved; that target remains open.
