# Surjectivity of a supplied common-closure reciprocity component

`CommonClosure.reciprocityUnits_surjective` is the existing private helper
from `Global.Arithmetic.UnitNormWeilStabilizerTransportProof`, moved to the
common-closure layer for reuse. Its field, extension and supplied reciprocity
family are unchanged. The map is the quotient projection to the abelianization
followed by the supplied equivalence; lifting the inverse image under that
equivalence proves surjectivity. The arithmetic transport proof and the rank-one
spectral wrapper share this proof. This makes no assertion that a reciprocity
family exists or satisfies normalization.
