# A Kummer root section of a Galois cover of a punctured regular local scheme

The module `Langlands.AlgebraicGeometry.FiniteEtale.TameRootSection` gives
the form of Abhyankar's lemma that the tame conjugation law needs. Over a
regular local scheme, a Galois cover of the complement of a regular divisor,
with group order invertible, is split by adjoining a root of the equation of
the divisor, after an étale neighbourhood of the closed point.

## Declarations

- `puncture t : Spec R[1/t] ⟶ Spec R` is `Spec.map` of the localization map
  `R → Localization.Away t`.
- `exists_root_section` assumes that `R` is a regular local ring
  (`IsRegularLocalRing R`), that `t : R` is nonzero with
  `IsRegularLocalRing (R ⧸ Ideal.span {t})`, and that `G` is a finite group
  with `IsUnit (Nat.card G : R)`. Let `W : Scheme.GaloisCover G (Spec R[1/t])`
  be a Galois cover. `Scheme.GaloisCover` is the structure of the pinned
  `weil-conjectures` package: a finite étale surjective `W.π : W.P ⟶ Y` with
  a left action of `G` over `Y` for which `∐_{g ∈ G} P → P ×_Y P` is an
  isomorphism. The theorem gives:
  - a ring `S` with a map `a : R ⟶ S` such that `Spec.map a` is étale, and a
    point `z` of `Spec S` with `Spec.map a z` the closed point of `Spec R`;
  - writing `g = a t`, `A = S[X]/(X ^ |G| - g)` (`AdjoinRoot`) and
    `V = D(g) ⊆ Spec A` (`PrimeSpectrum.basicOpen` of the image of `g`), a
    morphism `s : V ⟶ W.P` with
    `s ≫ W.π ≫ puncture t = V.ι ≫ Spec(S → A) ≫ Spec.map a`.

## Proof

`R` and `R/(t)` are regular rings: by the package lemma
`IsRegularLocalRing.localization_at_prime_and_isRegularRing`, every
localization at a prime of a regular local ring is regular. `t` is a nonzero
element of a domain, so it is a nonzerodivisor. The pullback of
`puncture t` along the identity of `Spec R` is identified with the basic open
`D(t)` of `Spec R` through Mathlib's `basicOpenIsoSpecAway`.

Let `Ω` be an algebraic closure of the residue field at the closed point and
`barY` the corresponding geometric point of `Spec R`. The package theorem
`AlgebraicGeometry.Scheme.GaloisCover.strict_hensel_root_section` gives a
section of `W` over the punctured Kummer cover
`D(t) ⊆ Spec Rˢʰ[X]/(X ^ |G| - t)` of the strict henselization `Rˢʰ` of `R`
at `barY` (Stacks Project, Tags 09EB, 0BRM, 0EYE, 0EYG). The package theorem
`AlgebraicGeometry.Scheme.punctured_root_section_etale_descent` then descends
the section to an étale neighbourhood. The ring `Rˢʰ` is the filtered colimit
of the coordinate rings of the pointed affine étale neighbourhoods of `barY`
(Stacks Project, Tag 0BSK). Correspondingly, the package lemma
`AlgebraicGeometry.Scheme.punctured_root_limit_presentation` writes the
punctured root scheme `D(t) ⊆ Spec Rˢʰ[X]/(X ^ |G| - t)` as the cofiltered
limit of the punctured root schemes `D(t) ⊆ Spec S[X]/(X ^ |G| - t)` over
these neighbourhoods. The target of the section is locally of finite
presentation over `Spec R`, so the section factors through one stage of this
limit (Stacks Project, Tag 05N9 and the descent paragraph of 0EYG). That
stage is an étale `R`-algebra `S` with a point over the closed point.
Removing the identity morphism from the resulting equation gives the stated
compatibility.
