# Isomorphisms and embeddings up to rank transport

Module `Langlands.Representation.Classification.MoeglinWaldspurgerCastCalculus`. Internal
infrastructure of the Aubert correctness proof of the Moeglin–Waldspurger recursion.

* `CastIso T X Y` (for `X` on `GL_r`, `Y` on `GL_s`): there is `h : r = s` with
  `T.castRank h X ≅ Y`. `Embeds T X Y`: there is `h : r = s` with `T.castRank h X` a
  subrepresentation of `Y`. Both absorb exact rank transports.
* `CastIso.refl/symm/trans`, `castIso_of_iso`, `castIso_castRank`, `CastIso.embeds`,
  `Embeds.trans`, `Embeds.castIso_right/left`, `embeds_of_isSubrepresentation`,
  `Embeds.isSubrepresentation_castRank`.
* `CastIso.binary`, `Embeds.binary`: the binary normalized product is compatible with both
  relations (by `subst`, functoriality and `binaryProductMap_injective`).
* `castIso_assoc`: for positive ranks, `(A × B) × C` and `A × (B × C)` are isomorphic up to the
  rank equality `Nat.add_assoc`. It converts the published
  `Aubert.GradedAssociativityProof.binaryAssocEquiv` (an equivalence after reindexing) using the
  published `castRankEquiv`.
