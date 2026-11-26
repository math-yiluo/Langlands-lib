# Uniform adic avatars of algebraic CM Hecke characters: the unconditional theorem

Module `Langlands.Galois.AlgebraicHeckeCharacterAvatarProof`, name space
`Langlands.GaloisRepresentation`. It proves `AlgebraicHeckeCharacterAvatarStatement` of
[`AlgebraicHeckeAvatarStatement`](AlgebraicHeckeAvatarStatement.md) without hypotheses.

```lean
theorem algebraicHeckeCharacterAvatar : AlgebraicHeckeCharacterAvatarStatement.{uK, uL}
```

The statement, as published (not changed): for every CM number field `K : Type uK` and every
Hecke character `χ` of `K` with `Harris.IsAlgebraic χ` (an integral infinity type, of any
weight), there are a number field `L : Type uL`, an embedding `ι : L →+* ℂ`, a finite set `S` of
finite places of `K`, values `a : FinitePlace K → Lˣ` and, for every finite place `λ` of `L`, a
continuous character `ψ λ : LambdaAdicCharacter K L λ` of the absolute Galois group of `K`, such
that `IsUniformHeckeAvatar ι χ S a ψ` holds:

* `S` is exactly the set of finite places at which `χ` is ramified;
* at every `v ∉ S` some uniformizer `π` of the completion `K_v` has
  `χ.finiteComponent v π = ι (a v)`;
* at every `v ∉ S` whose residue characteristic differs from that of `λ`, the character `ψ λ`
  kills inertia at `v` and sends every geometric Frobenius lift at `v` to the image of `a v` in
  the completion `L_λ`.

The universe parameters `uK` of the base field and `uL` of the coefficient field are
independent.

## Proof

The theorem is one application of the assembly theorem to four proved theorems:

```lean
algebraicHeckeAvatarAssembly.{uK, uL} algebraicHeckeFinitePart.{uK, uL}
  heckeAvatarIdeleCorrection.{uK, uL} finiteGeometricArtinLifting.{uK, uL}
  heckeAvatarInverseLimit.{uK, uL}
```

* `algebraicHeckeAvatarAssembly : AlgebraicHeckeAvatarAssemblyStatement.{uK, uL}`
  ([`AlgebraicHeckeAvatarAssemblyProof`](AlgebraicHeckeAvatarAssemblyProof.md)) proves
  `AlgebraicHeckeFinitePartStatement → HeckeAvatarIdeleCorrectionStatement →
  FiniteGeometricArtinLifting → HeckeAvatarInverseLimitStatement →
  AlgebraicHeckeCharacterAvatarStatement`, all at the universes `uK, uL`.
* `algebraicHeckeFinitePart : AlgebraicHeckeFinitePartStatement.{uK, uL}`
  ([`HeckeAvatarFinitePartProof`](HeckeAvatarFinitePartProof.md)): for a totally complex `K`
  and a Hecke character with integral infinity type, a number field `L` with `ι : L →+* ℂ`
  through which every complex embedding of `K` factors, a homomorphism `φ` from the finite
  ideles to `Lˣ` with open kernel whose composite with `ι` is the finite part of `χ`, and the
  exact set `S` of ramified finite places.
* `heckeAvatarIdeleCorrection : HeckeAvatarIdeleCorrectionStatement.{uK, uL}`
  ([`HeckeAvatarCorrectionProof`](HeckeAvatarCorrectionProof.md)): at each coefficient place
  `λ`, the corrected idele character descends to a continuous character of the idele classes
  with values in the completed integer units of `L_λ`, which agrees with the embedded `φ` on the
  local units at finite places of residue characteristic different from that of `λ`.
* `finiteGeometricArtinLifting : FiniteGeometricArtinLifting.{uK, uL}`
  ([`FiniteHeckeAvatarLiftProof`](FiniteHeckeAvatarLiftProof.md)), here with the coefficient
  universe `uA := uL`: the unique geometrically normalized lift of a finite idele-class character
  to the absolute Galois group. It is proved there from `finiteAbelianClassFieldExistence`
  (`Langlands/Global/Arithmetic/ClassFieldProof.lean`), `finiteArtinUnramifiedCriterion`
  (`Langlands/Global/Arithmetic/FiniteArtinUnramifiedCriterionProof.lean`) and
  `finiteUnramifiedGaloisRestriction`
  (`Langlands/Galois/FiniteUnramifiedGaloisRestrictionProof.lean`).
* `heckeAvatarInverseLimit : HeckeAvatarInverseLimitStatement.{uK, uL}`
  ([`HeckeAvatarInverseLimitProof`](HeckeAvatarInverseLimitProof.md)): if every congruence
  reduction of an integral idele-class character has a unique geometrically normalized lift
  outside `S`, these lifts are coherent and come from one continuous Galois character into the
  completed integer units, normalized in the same way outside `S`.

The universe arguments are written explicitly; each premise of the assembly theorem is used at the
same pair `uK, uL` as the conclusion. Lean reports that `algebraicHeckeCharacterAvatar` depends on
the axioms `propext`, `Classical.choice` and `Quot.sound` only.

## Sources

The construction follows Serre, *Abelian l-Adic Representations and Elliptic Curves*, Chapter II
§§2.3, 2.5 and 2.7, pp. II-10–II-12, II-18–II-20 and II-23–II-24 (`serre-abelian-l-adic-1989`).
The routes of the five combined proofs are described on their own pages, linked above.
