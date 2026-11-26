# Smooth proper lifts from twisted gluing data

Module `Langlands.AlgebraicGeometry.TwistedOpenGluingLift`. It combines
[`TwistedOpenGluingBaseChange`](TwistedOpenGluingBaseChange.md) and
[`SurjectiveClosedBaseChangeProper`](SurjectiveClosedBaseChangeProper.md).

## Setting

`D : Data C` is twisted gluing data over `π : C ⟶ S` (`hπ : D.IsOver π`), and
`t : T ⟶ S` is a closed immersion. A scheme `Y` with `q : Y ⟶ T` is covered by open
immersions `κ' i` of the pulled-back pieces of `D.baseChange hπ t`, satisfying the
hypotheses `hcov`, `hpre`, `hκ` of `Data.recognize`, and lying over `T`
(`hq : κ' i ≫ q = (V i).ι ≫ pullback.snd π t`).

## Declarations

In namespace `Langlands.AlgebraicGeometry.TwistedOpenGluing.Data`:

- `liftIso : Y ≅ pullback (D.toBase hπ) t`: the inverse of `recognize` followed by
  `baseChangeIso`. So `Y` is the reduction along `t` of the glued scheme.
- `liftIso_hom_snd`: `liftIso.hom ≫ pullback.snd (D.toBase hπ) t = q`, checked on the
  pieces of the pulled-back gluing.
- `isProper_toBase`: if moreover `t` is surjective, `q` is proper and `π` is locally of
  finite type, then `D.toBase hπ` is proper. Its base change along `t` is `q` up to the
  isomorphism `liftIso`, so `SurjectiveClosedBaseChange.isProper` applies.

In namespace `Langlands.AlgebraicGeometry`:

- `exists_section_lift φ hφ hnil p σ hσ`: let `φ : R' ⟶ R` be a surjection of commutative
  rings with nilpotent kernel and `p : X ⟶ Spec R'` smooth. Every section `σ` of
  `pullback.snd p (Spec.map φ)` lifts to a section `s` of `p` with
  `Spec.map φ ≫ s = σ ≫ pullback.fst p (Spec.map φ)`. This is the published infinitesimal
  lifting theorem `smoothThickeningLifting` applied to `σ ≫ pullback.fst p (Spec.map φ)`.

## Provenance

Internal assembly. It packages the construction of a smooth proper lift of a scheme from
compatible local lifts, as in Kai-Wen Lan, *Arithmetic compactifications of PEL-type
Shimura varieties*, Harvard thesis revised 14 March 2021, Proposition 2.1.2.2 (printed
p. 114, PDF p. 142), and the lifting of the identity section by smoothness invoked in
the proof of Proposition 2.2.2.3 (printed p. 145, PDF p. 173), registered as
`lan-2008-pel-thesis-revision-2021`, SHA-256
`a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079`.
